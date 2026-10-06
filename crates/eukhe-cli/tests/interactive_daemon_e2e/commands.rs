//! Attach, prompt, and slash-command verifiers: the daemon spawn, the
//! command menu, the model picker and effort, compaction, and the session tree.

use super::*;

#[tokio::test]
async fn tui_attaches_prompts_streams_lists_and_switches() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    let supervisor = spawn_supervisor(dir.path());

    // A second live session created through the daemon protocol, so the
    // switch target is known by id (not by list position).
    let script = serde_json::json!({ "responses": [
        { "text": "hello from scripted", "delayMs": 20 },
        { "text": "second turn" },
    ] });
    let second = create_session_via_daemon(
        &supervisor.socket,
        &dir.path().join("script.json"),
        &script,
        dir.path(),
        &session_dir,
    )
    .await;

    let options = eukhe_tui::interactive::InteractiveOptions {
        models: None,
        socket_path: supervisor.socket.clone(),
        cwd: dir.path().to_path_buf(),
        session_dir: Some(session_dir.clone()),
        script_path: Some(dir.path().join("script.json")),
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
    let plan = eukhe_tui::interactive::HeadlessPlan {
        steps: vec![
            eukhe_tui::interactive::HeadlessStep::Submit("hi".to_string()),
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 30_000 },
            eukhe_tui::interactive::HeadlessStep::Submit("again".to_string()),
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 30_000 },
            // Session list (the read-only info panel over the dock), then
            // close it and switch to the second session by id: the
            // transcript must rebuild from its (empty) snapshot and the next
            // prompt must run against the switched session.
            eukhe_tui::interactive::HeadlessStep::Submit("/list".to_string()),
            eukhe_tui::interactive::HeadlessStep::WaitRender {
                needle: "live sessions:".to_string(),
                timeout_ms: 30_000,
            },
            eukhe_tui::interactive::HeadlessStep::Key(crossterm::event::KeyEvent::new(
                crossterm::event::KeyCode::Esc,
                crossterm::event::KeyModifiers::NONE,
            )),
            eukhe_tui::interactive::HeadlessStep::Submit(format!("/switch {second}")),
            eukhe_tui::interactive::HeadlessStep::Submit("third".to_string()),
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 30_000 },
        ],
        width: 100,
        height: 30,
    };
    let outcome = run_headless_bounded(options, plan)
        .await
        .expect("interactive run");

    assert!(!outcome.frames.is_empty(), "frames were captured");
    let rendered = outcome.frames.join("\n");
    assert!(
        rendered.contains("hello from scripted"),
        "first scripted turn rendered:\n{rendered}"
    );
    assert!(
        rendered.contains("second turn"),
        "second scripted turn rendered:\n{rendered}"
    );
    assert!(rendered.contains("hi"), "user message echoed:\n{rendered}");
    assert!(
        rendered.contains("again"),
        "queued prompt rendered:\n{rendered}"
    );
    assert!(
        rendered.contains("live sessions:"),
        "session list rendered:\n{rendered}"
    );
    // After the switch, the third prompt ran against the switched session:
    // the scripted engine replays response 0 for it.
    assert!(
        rendered.contains("switched to session"),
        "switch note rendered:\n{rendered}"
    );
    assert_eq!(
        outcome.active_session_id, second,
        "the run ended attached to the switched session"
    );
    assert_eq!(
        outcome.last_assistant_text.as_deref(),
        Some("hello from scripted"),
        "the switched session produced its first scripted turn"
    );

    // Daemon-side verification: both sessions hold their turns.
    let (client, _events) = eukhe_tui::daemon_client::DaemonClient::connect(&supervisor.socket)
        .await
        .expect("connect supervisor");
    let last = client
        .request_ok(DaemonCommand::GetLastAssistantText {
            id: None,
            active_session_id: second.clone(),
            rest: serde_json::Map::default(),
        })
        .await
        .expect("get_last_assistant_text");
    assert_eq!(last["text"], "hello from scripted");
    let sessions = client
        .request_ok(DaemonCommand::List {
            id: None,
            all: None,
            cwd: None,
            session_dir: None,
            include_client_owned: None,
            rest: serde_json::Map::default(),
        })
        .await
        .expect("list");
    assert_eq!(
        sessions["sessions"].as_array().map(Vec::len),
        Some(2),
        "both sessions stay live after the TUI exited: {sessions}"
    );
    client.close();

    // The session files are on disk (reattach survives a TUI restart).
    let persisted = std::fs::read_dir(&session_dir)
        .expect("read session dir")
        .flatten()
        .filter(|entry| entry.path().extension().and_then(|e| e.to_str()) == Some("jsonl"))
        .count();
    assert_eq!(persisted, 2, "two session files persisted");
    drop(supervisor);
}

/// The product launch path: `ensure_daemon_running` spawns a detached
/// `eukhe --mode daemon` when nothing is listening, then the TUI
/// attaches through it.
#[tokio::test]
async fn ensure_daemon_running_spawns_supervisor_and_tui_attaches() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    let socket = dir.path().join("spawned.sock");
    std::env::set_var("EUKHE_CODING_AGENT_DIR", &agent_dir);
    // The internally-spawned supervisor inherits this process's env: give
    // its session workers the short supervisor-lost exit window so a killed
    // supervisor cannot leak them into later test binaries (the
    // `spawn_supervisor` fixture sets the same variable on its children).
    std::env::set_var(
        eukhe_daemon::worker::WORKER_SUPERVISOR_LOST_EXIT_MS_ENV,
        "15000",
    );

    let script_path = dir.path().join("script.json");
    std::fs::write(
        &script_path,
        serde_json::json!({ "responses": [{ "text": "spawned hello" }] }).to_string(),
    )
    .expect("write script");

    let options = eukhe_tui::interactive::InteractiveOptions {
        models: None,
        socket_path: socket.clone(),
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
        initial_message: Some("boot".to_string()),
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
    // The interactive runtime's own launch sequence, minus the TTY: spawn
    // the real supervisor binary detached and wait for the hello handshake.
    let _guard = DetachedDaemon {
        socket: socket.clone(),
    };
    let exe = std::path::PathBuf::from(env!("CARGO_BIN_EXE_eukhe"));
    eukhe_cli::ensure_daemon_running_with(&exe, &socket, dir.path())
        .await
        .expect("spawn the daemon");
    let plan = eukhe_tui::interactive::HeadlessPlan {
        steps: vec![eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 30_000 }],
        width: 80,
        height: 24,
    };
    let outcome = run_headless_bounded(options, plan)
        .await
        .expect("headless interactive run");
    assert!(
        outcome
            .frames
            .iter()
            .any(|frame| frame.contains("spawned hello")),
        "initial message ran against the spawned daemon:\n{}",
        outcome.frames.join("\n")
    );
    assert_eq!(
        outcome.last_assistant_text.as_deref(),
        Some("spawned hello")
    );

    // The product contract under test: shut the spawned supervisor down by
    // protocol and require the process tree to actually exit (the guard
    // stays as the panic backstop; this call asserts the clean stop).
    assert_daemon_stops_clean(&socket);
}

/// Slash-command dispatch over a live scripted session: the session command
/// executes in the worker (durable echo + result rows reach the transcript
/// and the session file), client commands without a UI report
/// unavailability, unknown commands get the TS suggestion error, and the
/// autocomplete menu renders from the shared registry.
#[tokio::test]
async fn tui_dispatches_slash_commands_menu_and_suggestions() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    let supervisor = spawn_supervisor(dir.path());

    // The faux engine (`engine: "faux"`) drives the real agent engine over
    // the scripted faux provider, so the worker's session-command admission
    // path runs exactly as in the product.
    let script = serde_json::json!({ "engine": "faux", "responses": [
        { "text": "scripted reply" },
    ] });
    std::fs::write(dir.path().join("script.json"), script.to_string()).expect("write script");
    let options = eukhe_tui::interactive::InteractiveOptions {
        models: None,
        socket_path: supervisor.socket.clone(),
        cwd: dir.path().to_path_buf(),
        session_dir: Some(session_dir.clone()),
        script_path: Some(dir.path().join("script.json")),
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
    let plan = eukhe_tui::interactive::HeadlessPlan {
        steps: vec![
            // A session command runs in the worker and its durable rows
            // render (echo + result).
            eukhe_tui::interactive::HeadlessStep::Submit("/goal status".to_string()),
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 30_000 },
            // Unknown command: the exact TS suggestion error.
            eukhe_tui::interactive::HeadlessStep::Submit("/modle".to_string()),
            // The autocomplete menu: typed input like a user keystroke by
            // keystroke, completed with Enter, then submitted.
            eukhe_tui::interactive::HeadlessStep::Type("/".to_string()),
            // A real user pauses between keystrokes: the parked suggestion
            // request materializes (the dropdown opens) before Enter, the
            // state the terminal loop reaches after one input-idle tick.
            eukhe_tui::interactive::HeadlessStep::SettleIdle,
            eukhe_tui::interactive::HeadlessStep::Type("goa".to_string()),
            eukhe_tui::interactive::HeadlessStep::SettleIdle,
            // With the dropdown open, Enter completes the selected
            // suggestion (`/goal `); the second Enter submits it.
            eukhe_tui::interactive::HeadlessStep::Type("\n".to_string()),
            eukhe_tui::interactive::HeadlessStep::Type("\n".to_string()),
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 30_000 },
            // `/model` LAST: the inline menu-panel opens and owns the keys
            // from here on (TS `showConfigurationMenu`).
            eukhe_tui::interactive::HeadlessStep::Submit("/model".to_string()),
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 30_000 },
        ],
        width: 120,
        height: 36,
    };
    let outcome = run_headless_bounded(options, plan)
        .await
        .expect("interactive run");

    // Verification seam: dump the captured frames for manual frame-diffing
    // against the TS product (EUKHE_TUI_DUMP_FRAMES=<dir>).
    if let Ok(dir) = std::env::var("EUKHE_TUI_DUMP_FRAMES") {
        for (index, frame) in outcome.frames.iter().enumerate() {
            let _ = std::fs::write(
                std::path::Path::new(&dir).join(format!("frame-{index:03}.txt")),
                frame,
            );
        }
    }
    let rendered = outcome.frames.join("\n");
    assert!(
        rendered.contains("/goal status"),
        "the session-command echo row rendered:\n{rendered}"
    );
    assert!(
        rendered.contains("No active goal."),
        "the session-command result row rendered:\n{rendered}"
    );
    assert!(
        rendered.contains("Unknown command: /modle. Did you mean /model?"),
        "the unknown-command suggestion matched the TS string:\n{rendered}"
    );
    assert!(
        rendered.contains("Search models"),
        "the /model command opened the inline menu-panel:\n{rendered}"
    );
    assert!(
        rendered.contains("Enter select - Esc close"),
        "the menu-panel hint rendered:\n{rendered}"
    );
    // The menu: the first registry entry is selected at `/`, and `/goa`
    // fuzzy-matches to the goal command.
    assert!(
        rendered.contains("> settings"),
        "the slash menu rendered with the selected first entry:\n{rendered}"
    );
    assert!(
        rendered.contains("Open settings menu"),
        "the selected item's description rendered:\n{rendered}"
    );
    assert!(
        rendered.contains("> goal"),
        "the fuzzy best match for /goa rendered selected:\n{rendered}"
    );

    // The durable rows persisted: the session file carries the echo and
    // result custom entries for both executions.
    let mut saw_echo = false;
    let mut saw_result = false;
    for entry in std::fs::read_dir(&session_dir)
        .expect("read session dir")
        .flatten()
    {
        let path = entry.path();
        if path.extension().and_then(|e| e.to_str()) != Some("jsonl") {
            continue;
        }
        let content = std::fs::read_to_string(&path).unwrap_or_default();
        saw_echo |= content.contains("\"session_slash_command\"");
        saw_result |= content.contains("\"session_slash_command_result\"");
    }
    assert!(
        saw_echo,
        "the session file persisted the session_slash_command rows"
    );
    assert!(
        saw_result,
        "the session file persisted the session_slash_command_result rows"
    );
    drop(supervisor);
}

/// The `/model` picker + `/effort` surface, end to end through the daemon:
/// a models.json custom model lists in the picker (name label), Enter
/// applies it through the daemon `set_model` command (durable `model_change`
/// row + the TS `Model: <id>` confirm row), and `/effort` on a model without
/// reasoning reports the TS unsupported note (the thinking-level plumbing:
/// the worker reports the model's supported levels, the client treats an
/// `off`-only list as no thinking).
#[tokio::test]
async fn tui_model_picker_applies_and_effort_reports() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    // The battery layout: a custom provider in models.json carries the
    // model (id, name, endpoint), so it resolves without any network.
    std::fs::write(
        agent_dir.join("models.json"),
        serde_json::json!({
            "providers": {
                "test-provider": {
                    "api": "openai-completions",
                    "baseUrl": "http://127.0.0.1:9/v1",
                    "apiKey": "sk-test",
                    "models": [
                        { "id": "mock-1", "name": "Mock 1", "api": "openai-completions",
                          "baseUrl": "http://127.0.0.1:9/v1", "contextWindow": 128_000,
                          "maxTokens": 4096 }
                    ]
                }
            }
        })
        .to_string(),
    )
    .expect("write models.json");
    let script = serde_json::json!({ "engine": "faux", "responses": [
        { "text": "scripted reply" },
    ] });
    std::fs::write(dir.path().join("script.json"), script.to_string()).expect("write script");
    let supervisor = spawn_supervisor(dir.path());
    // The catalog snapshot the composition root injects (available models
    // over the same registry). The registry scope is pinned hermetically:
    // the auth storage reads no ambient environment, so an ambient provider
    // credential (PRIME_API_KEY on the dev box makes every bundled
    // prime-inference model available) cannot leak the bundled catalog in —
    // the models.json mock is the ONLY available model, per the assertion's
    // intent. `spawn_supervisor` strips the same variables from the daemon
    // side.
    let auth = eukhe_core::auth::AuthStorage::in_memory_without_env(
        &eukhe_core::auth::AuthStorageData::default(),
        std::sync::Arc::new(eukhe_core::auth::NoOAuth),
    );
    let mut registry =
        eukhe_core::models::ModelRegistry::create(auth, agent_dir.join("models.json"));
    registry.load_private_authorization_from_cache();
    let catalog: Vec<eukhe_types::ai::Model> =
        registry.get_available().into_iter().cloned().collect();
    assert_eq!(catalog.len(), 1, "the models.json model resolves available");
    assert_eq!(
        catalog[0].id, "mock-1",
        "the one available model is the models.json mock"
    );

    let options = eukhe_tui::interactive::InteractiveOptions {
        models: None,
        socket_path: supervisor.socket.clone(),
        cwd: dir.path().to_path_buf(),
        session_dir: Some(session_dir.clone()),
        script_path: Some(dir.path().join("script.json")),
        model_selection: eukhe_tui::interactive::ModelSelection::default(),
        model_catalog: catalog,
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
    let plan = eukhe_tui::interactive::HeadlessPlan {
        steps: vec![
            eukhe_tui::interactive::HeadlessStep::Submit("/model".to_string()),
            eukhe_tui::interactive::HeadlessStep::Type("mock".to_string()),
            eukhe_tui::interactive::HeadlessStep::Type("\n".to_string()),
            eukhe_tui::interactive::HeadlessStep::Submit("/effort".to_string()),
            // ctrl+l opens the picker over the user's own text: the pick
            // must keep it (TS's selector never touches the editor).
            eukhe_tui::interactive::HeadlessStep::Type("keep me".to_string()),
            eukhe_tui::interactive::HeadlessStep::Key(crossterm::event::KeyEvent::new(
                crossterm::event::KeyCode::Char('l'),
                crossterm::event::KeyModifiers::CONTROL,
            )),
            eukhe_tui::interactive::HeadlessStep::WaitRender {
                needle: "Search models".to_string(),
                timeout_ms: 30_000,
            },
            eukhe_tui::interactive::HeadlessStep::Key(crossterm::event::KeyEvent::new(
                crossterm::event::KeyCode::Enter,
                crossterm::event::KeyModifiers::NONE,
            )),
        ],
        width: 120,
        height: 36,
    };
    let outcome = run_headless_bounded(options, plan)
        .await
        .expect("interactive run");
    let rendered = outcome.frames.join("\n");
    assert!(
        rendered.contains("Mock 1"),
        "the /model picker listed the models.json model by name:\n{rendered}"
    );
    assert!(
        rendered.contains("Model: mock-1"),
        "picking the model showed the TS confirm row:\n{rendered}"
    );
    assert!(
        rendered.contains("Current model does not support thinking"),
        "the /effort command reported the TS unsupported-model note:\n{rendered}"
    );

    // The durable rows persisted: the creation-prefix `model_change` plus
    // the switch's own row (TS `appendModelChange` runs on every switch,
    // even to the current model).
    let mut model_changes = 0;
    for entry in std::fs::read_dir(&session_dir)
        .expect("read session dir")
        .flatten()
    {
        let path = entry.path();
        if path.extension().and_then(|e| e.to_str()) != Some("jsonl") {
            continue;
        }
        let content = std::fs::read_to_string(&path).unwrap_or_default();
        model_changes += content
            .lines()
            .filter(|line| line.contains(r#""type":"model_change""#))
            .count();
    }
    assert!(
        model_changes >= 2,
        "the set_model switch persisted its model_change row (saw {model_changes})"
    );
    // The ctrl+l pick kept the editor's own text: the final frame's prompt
    // row still carries it (an apply-side clear would leave it empty).
    let last = outcome.frames.last().expect("a final frame");
    assert!(
        last.contains("keep me"),
        "the ctrl+l pick kept the editor's own text:\n{last}"
    );
    drop(supervisor);
}

/// `/effort` on a thinking-capable model whose `reasoning` flag is false
/// but whose `thinkingLevelMap` declares addressable levels (the live
/// catalog's `gpt-5.3-chat-latest` shape): the map is the capability
/// signal, so the command applies the level instead of reporting the
/// unsupported-model note. No scripted engine runs — the switch and the
/// state read must resolve the models.json model, not the faux one.
#[tokio::test]
async fn tui_effort_applies_on_a_map_addressable_model_without_the_reasoning_flag() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    std::fs::write(
        agent_dir.join("models.json"),
        serde_json::json!({
            "providers": {
                "test-provider": {
                    "api": "openai-completions",
                    "baseUrl": "http://127.0.0.1:9/v1",
                    "apiKey": "sk-test",
                    "models": [
                        { "id": "chat-plus", "name": "Chat Plus", "reasoning": false,
                          "thinkingLevelMap": { "off": null, "xhigh": "xhigh" },
                          "baseUrl": "http://127.0.0.1:9/v1", "contextWindow": 128_000,
                          "maxTokens": 4096 }
                    ]
                }
            }
        })
        .to_string(),
    )
    .expect("write models.json");
    let supervisor = spawn_supervisor(dir.path());
    let auth = eukhe_core::auth::AuthStorage::in_memory_without_env(
        &eukhe_core::auth::AuthStorageData::default(),
        std::sync::Arc::new(eukhe_core::auth::NoOAuth),
    );
    let mut registry =
        eukhe_core::models::ModelRegistry::create(auth, agent_dir.join("models.json"));
    registry.load_private_authorization_from_cache();
    let catalog: Vec<eukhe_types::ai::Model> =
        registry.get_available().into_iter().cloned().collect();
    assert_eq!(catalog.len(), 1, "the models.json model resolves available");
    assert_eq!(catalog[0].id, "chat-plus");

    let options = eukhe_tui::interactive::InteractiveOptions {
        models: None,
        socket_path: supervisor.socket.clone(),
        cwd: dir.path().to_path_buf(),
        session_dir: Some(session_dir.clone()),
        script_path: None,
        model_selection: eukhe_tui::interactive::ModelSelection::default(),
        model_catalog: catalog,
        model_configured_providers: ["test-provider".to_string()].into_iter().collect(),
        model_recent_models: Vec::new(),
        default_thinking_level: None,
        no_session: false,
        session: eukhe_tui::interactive::SessionSelection::New,
        show_images: true,
        screen_mode: eukhe_tui::screen_mode::ScreenMode::Inline,
        client_settings: None,
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
    };
    let plan = eukhe_tui::interactive::HeadlessPlan {
        steps: vec![
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 30_000 },
            eukhe_tui::interactive::HeadlessStep::Submit("/model".to_string()),
            eukhe_tui::interactive::HeadlessStep::Type("chat".to_string()),
            eukhe_tui::interactive::HeadlessStep::Type("\n".to_string()),
            eukhe_tui::interactive::HeadlessStep::Submit("/effort xhigh".to_string()),
        ],
        width: 120,
        height: 36,
    };
    let outcome = run_headless_bounded(options, plan)
        .await
        .expect("interactive run");
    let rendered = outcome.frames.join("\n");
    assert!(
        rendered.contains("Model: chat-plus"),
        "picking the model showed the TS confirm row:\n{rendered}"
    );
    assert!(
        rendered.contains("Thinking level: xhigh"),
        "the /effort command applied the map's addressable level:\n{rendered}"
    );
    assert!(
        !rendered.contains("Current model does not support thinking"),
        "a map-addressable model must not report the unsupported-model note:\n{rendered}"
    );

    // The durable `thinking_level_change` row persisted for the applied
    // level (TS `appendThinkingLevelChange` on an effective change).
    let mut level_changes = 0;
    for entry in std::fs::read_dir(&session_dir)
        .expect("read session dir")
        .flatten()
    {
        let path = entry.path();
        if path.extension().and_then(|e| e.to_str()) != Some("jsonl") {
            continue;
        }
        let content = std::fs::read_to_string(&path).unwrap_or_default();
        level_changes += content
            .lines()
            .filter(|line| line.contains(r#""type":"thinking_level_change""#))
            .filter(|line| line.contains("xhigh"))
            .count();
    }
    assert!(
        level_changes >= 1,
        "the thinking_level_change row persisted at xhigh (saw {level_changes})"
    );
    drop(supervisor);
}

/// `/compact` on a fresh session: the compaction skips (TS
/// `CompactionSkippedError`) and the warning reaches the transcript through
/// the `compaction_end` event, with the durable echo row — TS's live
/// `showWarning` on the manual compaction path.
#[tokio::test]
async fn tui_compact_on_a_short_session_warns_nothing_to_compact() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    let supervisor = spawn_supervisor(dir.path());

    // The real agent engine over the scripted faux provider: the skip path
    // never reaches the provider, so the script stays unused.
    let script = serde_json::json!({ "engine": "faux", "responses": [] });
    std::fs::write(dir.path().join("script.json"), script.to_string()).expect("write script");
    let options = eukhe_tui::interactive::InteractiveOptions {
        models: None,
        socket_path: supervisor.socket.clone(),
        cwd: dir.path().to_path_buf(),
        session_dir: Some(session_dir.clone()),
        script_path: Some(dir.path().join("script.json")),
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
    let plan = eukhe_tui::interactive::HeadlessPlan {
        steps: vec![
            eukhe_tui::interactive::HeadlessStep::Submit("/compact".to_string()),
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 30_000 },
        ],
        width: 100,
        height: 30,
    };
    let outcome = run_headless_bounded(options, plan)
        .await
        .expect("interactive run");
    // Verification seam: dump the captured frames for manual frame-diffing
    // against the TS product (EUKHE_TUI_DUMP_FRAMES=<dir>).
    if let Ok(dump) = std::env::var("EUKHE_TUI_DUMP_FRAMES") {
        for (index, frame) in outcome.frames.iter().enumerate() {
            let _ = std::fs::write(
                std::path::Path::new(&dump).join(format!("skip-frame-{index:03}.txt")),
                frame,
            );
        }
    }
    let rendered = outcome.frames.join("\n");
    assert!(
        rendered.contains("/compact"),
        "the session-command echo row rendered:\n{rendered}"
    );
    assert!(
        rendered.contains("Session is too short to compact"),
        "the skip warning rendered (TS compaction_end errorMessage):\n{rendered}"
    );
    // The skip records no durable result row (TS's queued-command catch arm
    // stays silent): only the echo row persisted.
    let mut saw_compaction_entry = false;
    let mut saw_result_row = false;
    for entry in std::fs::read_dir(&session_dir)
        .expect("read session dir")
        .flatten()
    {
        let path = entry.path();
        if path.extension().and_then(|e| e.to_str()) != Some("jsonl") {
            continue;
        }
        let content = std::fs::read_to_string(&path).unwrap_or_default();
        saw_compaction_entry |= content.contains("\"type\":\"compaction\"");
        saw_result_row |= content.contains("\"session_slash_command_result\"");
    }
    assert!(
        !saw_compaction_entry,
        "a skipped compaction persisted no compaction entry"
    );
    assert!(
        !saw_result_row,
        "a skipped compaction persisted no result row"
    );
    drop(supervisor);
}

/// `/compact` on a grown session: the compaction loader replaces the working
/// loader while the summarizer runs (TS `startCompactionLoader`), then the
/// summary row renders (TS `CompactionSummaryMessageComponent`) at the head
/// of the rebuilt transcript (TS `rebuildChatFromMessages`). The loader row
/// is a soft evidence capture (its in-flight window is delayMs-paced and a
/// loaded box can batch the whole window past the paint loop);
/// the settled outcome — the summary row, the rebuilt transcript, and the
/// retained tail — carries the hard asserts.
#[tokio::test]
async fn tui_compact_shows_the_loader_then_the_summary_and_rebuilds() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    // TS `getCompactionSettings` feeds every compaction path, `/compact`
    // included: the settings-pinned cut budget keeps this run small while
    // exercising the same keep-recent cut the default budget drives.
    std::fs::write(
        agent_dir.join("settings.json"),
        serde_json::json!({ "compaction": { "keepRecentTokens": 10 } }).to_string(),
    )
    .expect("write settings");
    let supervisor = spawn_supervisor(dir.path());

    // The session shape (TS-binary-verified): a large
    // first turn gives the compactor history to summarize, the small
    // second turn crosses the 10-token keep-recent budget AT its user
    // message — a non-split cut that keeps the whole second turn — and
    // the third scripted response is the summarizer's summary. Its delay
    // holds the compaction in flight for the loader window: 1.5s is the
    // load-realistic bound (the healthy loop paints hundreds of frames
    // in that window, so the loader evidence below still captures on the
    // mission box's ambient daemon load — at the original 300ms the loop
    // stalled past the window in ~half the runs, batching the start and
    // finish events into one iteration). The cut must stay on the user
    // message: a mid-turn (assistant) cut is a split-turn compaction that
    // makes TWO summarizer wire calls (TS parity), which this
    // single-summary script does not serve.
    let filler = "history ".repeat(150);
    let script = serde_json::json!({
        "engine": "faux",
        "responses": [
            { "text": filler, "delayMs": 20 },
            { "text": "second turn done, kept intact" },
            { "text": "## Summary\nthe session story", "delayMs": 1500 },
        ],
    });
    std::fs::write(dir.path().join("script.json"), script.to_string()).expect("write script");
    let options = eukhe_tui::interactive::InteractiveOptions {
        models: None,
        socket_path: supervisor.socket.clone(),
        cwd: dir.path().to_path_buf(),
        session_dir: Some(session_dir.clone()),
        script_path: Some(dir.path().join("script.json")),
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
    let ctrl_o = || {
        eukhe_tui::interactive::HeadlessStep::Key(crossterm::event::KeyEvent::new(
            crossterm::event::KeyCode::Char('o'),
            crossterm::event::KeyModifiers::CONTROL,
        ))
    };
    let plan = eukhe_tui::interactive::HeadlessPlan {
        steps: vec![
            eukhe_tui::interactive::HeadlessStep::Submit("first".to_string()),
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 30_000 },
            eukhe_tui::interactive::HeadlessStep::Submit(
                "second, and please keep this second parity turn short and intact".to_string(),
            ),
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 30_000 },
            eukhe_tui::interactive::HeadlessStep::Submit("/compact focus on the goal".to_string()),
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 30_000 },
            // The collapsible block (TS `applyChatExpansion` fanning
            // `toolOutputExpanded` into `CompactionSummaryMessageComponent`):
            // Ctrl+O twice walks overview -> details -> all, expanding the
            // summary into the markdown body plus the token metadata; the
            // third press wraps back to overview and re-collapses it.
            ctrl_o(),
            ctrl_o(),
            eukhe_tui::interactive::HeadlessStep::SettleIdle,
            ctrl_o(),
            eukhe_tui::interactive::HeadlessStep::SettleIdle,
        ],
        width: 100,
        height: 30,
    };
    let outcome = run_headless_bounded(options, plan)
        .await
        .expect("interactive run");

    // Verification seam: dump the captured frames for manual frame-diffing
    // against the TS product (EUKHE_TUI_DUMP_FRAMES=<dir>).
    if let Ok(dump) = std::env::var("EUKHE_TUI_DUMP_FRAMES") {
        for (index, frame) in outcome.frames.iter().enumerate() {
            let _ = std::fs::write(
                std::path::Path::new(&dump).join(format!("compact-frame-{index:03}.txt")),
                frame,
            );
        }
    }
    let rendered = outcome.frames.join("\n");
    // The loader (TS `Compacting context (focus: ...)... (Ctrl+C to
    // cancel)`) is a soft, best-effort capture: its in-flight window is
    // delayMs-paced, and on a box loaded by the fleet's daemons the render
    // loop can stall past the whole window — the compaction-started and
    // compaction-finished events then apply in one batched iteration (the
    // loop drains the queued events before it paints), so no captured frame
    // ever shows the loader row. Any finite pacing window leaves that race,
    // so frame-level loader assertions belong in a sandboxed run on an
    // idle box. Here the observed loader row is evidence only; the hard
    // asserts below pin the settled outcome — the parity-critical claims.
    let loader = "Compacting context (focus: focus on the goal)... (Ctrl+C to cancel)";
    let loader_frames = outcome
        .frames
        .iter()
        .filter(|frame| frame.contains(loader))
        .count();
    println!(
        "compaction loader evidence: {loader_frames} frames captured the loader row (soft check)"
    );
    // The summary row: the TS header plus the collapsed summary.
    assert!(
        rendered.contains("* Context compacted"),
        "the compaction summary header rendered:\n{rendered}"
    );
    assert!(
        rendered.contains("the session story"),
        "the summary text rendered:\n{rendered}"
    );
    // The rebuilt transcript presents the retained tail first, then the
    // summary (TS `orderMessagesForTranscript`): the settled bottom-follow
    // frame shows the retained second turn above the summary row, and the
    // compacted-away first turn is gone.
    let last = outcome.frames.last().expect("the settled frame");
    assert!(
        last.contains("kept intact"),
        "the retained second turn heads the rebuilt transcript:\n{last}"
    );
    assert!(
        last.contains("* Context compacted"),
        "the summary row follows the retained tail:\n{last}"
    );
    assert!(
        !last.contains("first"),
        "the compacted-away first turn dropped from the rebuilt transcript:\n{last}"
    );

    // The collapsible block: the expanded frames show the markdown body and
    // the dim metadata row (TS `new Markdown(summary, ...)` + the
    // `Compacted from N tokens \u{b7} focus: ...` row); the wrap back to
    // overview re-collapses (the `EventSummary` returns, metadata gone).
    let expanded = outcome
        .frames
        .iter()
        .find(|frame| frame.contains("Compacted from"))
        .expect("some frame captured the expanded compaction block");
    assert!(
        expanded.contains("Compacted from") && expanded.contains("tokens"),
        "the expanded metadata row:\n{expanded}"
    );
    assert!(
        expanded.contains(" - focus: focus on the goal"),
        "the /compact focus rides the expanded metadata:\n{expanded}"
    );
    assert!(
        expanded.contains("Summary") && !expanded.contains("## Summary"),
        "the expanded body renders the summary markdown, not the EventSummary flatten:\n{expanded}"
    );
    assert!(
        !last.contains("Compacted from"),
        "the third Ctrl+O re-collapsed the block:\n{last}"
    );

    // The compaction entry persisted (the durable `compaction` record).
    let mut saw_compaction_entry = false;
    for entry in std::fs::read_dir(&session_dir)
        .expect("read session dir")
        .flatten()
    {
        let path = entry.path();
        if path.extension().and_then(|e| e.to_str()) != Some("jsonl") {
            continue;
        }
        let content = std::fs::read_to_string(&path).unwrap_or_default();
        saw_compaction_entry |= content.contains("\"type\":\"compaction\"");
    }
    assert!(
        saw_compaction_entry,
        "the compaction entry persisted to the session file"
    );
    drop(supervisor);
}

/// Session-tree verifier: two scripted turns, then `/tree` navigation back
/// to the first user message, a fork from it, and a clone at the leaf.
/// Exercises the full loop the TS `/tree` surface owns: the `get_session_tree`
/// fetch, the selector pane, the "Summarize branch?" choice, `navigate_tree`
/// (branch move + transcript rebuild + editor text restore), `fork` (new
/// session file), and the leaf no-op.
#[tokio::test]
async fn tui_session_tree_navigates_forks_and_clones() {
    use crossterm::event::{KeyCode, KeyModifiers};

    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    let supervisor = spawn_supervisor(dir.path());
    let script = serde_json::json!({
        "engine": "faux",
        "responses": [
            { "text": "first answer", "delayMs": 10 },
            { "text": "second answer", "delayMs": 10 },
            { "text": "post-fork answer", "delayMs": 10 },
        ],
    });
    std::fs::write(dir.path().join("script.json"), script.to_string()).expect("write script");
    let options = eukhe_tui::interactive::InteractiveOptions {
        models: None,
        socket_path: supervisor.socket.clone(),
        cwd: dir.path().to_path_buf(),
        session_dir: Some(session_dir.clone()),
        script_path: Some(dir.path().join("script.json")),
        model_selection: eukhe_tui::interactive::ModelSelection::default(),
        model_catalog: Vec::new(),
        model_configured_providers: std::collections::HashSet::default(),
        model_recent_models: Vec::new(),
        default_thinking_level: None,
        no_session: false,
        session: eukhe_tui::interactive::SessionSelection::New,
        initial_message: None,
        theme: "eukhe".to_string(),
        code_block_indent: "  ".to_string(),
        // The default tree filter keeps every message row visible, and the
        // branch-summary prompt is skipped so navigation needs no
        // summarizer call (TS `branchSummary.skipPrompt`).
        tree_filter_mode: "default".to_string(),
        branch_summary_skip_prompt: true,
        show_images: true,
        screen_mode: eukhe_tui::screen_mode::ScreenMode::Inline,
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
    let key = |code: KeyCode| {
        eukhe_tui::interactive::HeadlessStep::Key(crossterm::event::KeyEvent::new(
            code,
            KeyModifiers::NONE,
        ))
    };
    let enter = key(KeyCode::Enter);
    let up = key(KeyCode::Up);
    let plan = eukhe_tui::interactive::HeadlessPlan {
        steps: vec![
            eukhe_tui::interactive::HeadlessStep::Submit("first question".to_string()),
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 30_000 },
            eukhe_tui::interactive::HeadlessStep::Submit("second question".to_string()),
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 30_000 },
            // `/tree` opens the selector; Enter on the leaf is the TS no-op.
            eukhe_tui::interactive::HeadlessStep::Submit("/tree".to_string()),
            eukhe_tui::interactive::HeadlessStep::SettleIdle,
            enter.clone(),
            eukhe_tui::interactive::HeadlessStep::SettleIdle,
            // `/fork` opens the user-message selector; Enter forks before
            // the selected (latest) user message.
            eukhe_tui::interactive::HeadlessStep::Submit("/fork".to_string()),
            eukhe_tui::interactive::HeadlessStep::SettleIdle,
            enter.clone(),
            eukhe_tui::interactive::HeadlessStep::SettleIdle,
            // The fork re-entered the user message in the editor; submit
            // runs it on the forked session.
            enter.clone(),
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 30_000 },
            // `/tree` again, then navigate two rows up (the first answer)
            // to cut the branch back to that point.
            eukhe_tui::interactive::HeadlessStep::Submit("/tree".to_string()),
            eukhe_tui::interactive::HeadlessStep::SettleIdle,
            up.clone(),
            up.clone(),
            enter.clone(),
            eukhe_tui::interactive::HeadlessStep::SettleIdle,
        ],
        width: 100,
        height: 34,
    };
    let outcome = run_headless_bounded(options, plan)
        .await
        .expect("interactive run");
    if let Ok(dump) = std::env::var("EUKHE_TUI_DUMP_FRAMES") {
        for (index, frame) in outcome.frames.iter().enumerate() {
            let _ = std::fs::write(
                std::path::Path::new(&dump).join(format!("tree-frame-{index:03}.txt")),
                frame,
            );
        }
    }
    let rendered = outcome.frames.join("\n");
    // The selector pane (TS `TreeSelectorComponent` layout).
    assert!(
        rendered.contains("Session Tree"),
        "the tree pane rendered:\n{rendered}"
    );
    assert!(
        rendered.contains("Type to search:"),
        "the search line rendered:\n{rendered}"
    );
    assert!(
        rendered.contains("user: first question") && rendered.contains("user: second question"),
        "the entry rows rendered:\n{rendered}"
    );
    // The leaf no-op note (TS `showStatus("Already at this point")`).
    assert!(
        rendered.contains("Already at this point"),
        "the leaf selection was a no-op:\n{rendered}"
    );
    // The fork (TS `showUserMessageSelector` + `showStatus("Forked to new
    // session")`).
    assert!(
        rendered.contains("Fork from Message"),
        "the fork selector rendered:\n{rendered}"
    );
    assert!(
        rendered.contains("Forked to new session"),
        "the fork note rendered:\n{rendered}"
    );
    // The forked session kept the pre-fork path and answered the re-entered
    // user message with its own scripted turn.
    assert!(
        rendered.contains("post-fork answer"),
        "the forked session ran a turn:\n{rendered}"
    );
    // The navigation: TS `showStatus("Navigated to selected point")` plus
    // the transcript rebuilt on the moved branch (the abandoned turn drops
    // from the settled frame).
    assert!(
        rendered.contains("Navigated to selected point"),
        "the navigation note rendered:\n{rendered}"
    );
    let settled = outcome
        .frames
        .iter()
        .rev()
        .find(|frame| frame.contains("Navigated to selected point"))
        .expect("the navigation frame");
    assert!(
        !settled.contains("post-fork answer"),
        "the abandoned branch dropped from the rebuilt transcript:\n{settled}"
    );
    assert!(
        settled.contains("first answer"),
        "the moved branch kept the target path:\n{settled}"
    );
    // The fork created a second session file.
    let session_files: Vec<_> = std::fs::read_dir(&session_dir)
        .expect("read session dir")
        .flatten()
        .filter(|entry| entry.path().extension().and_then(|e| e.to_str()) == Some("jsonl"))
        .collect();
    assert!(
        session_files.len() >= 2,
        "the fork wrote a new session file: {} files",
        session_files.len()
    );
    drop(supervisor);
}
