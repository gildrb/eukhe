//! Prompt-stash verifiers: the draft round trips across switches, the
//! agents-view handoff, pasted images, Ctrl+S, and queue browsing.

use super::*;

/// Prompt-stash verifier (TS `prompt-stash-state.ts` + the
/// interactive-mode stash call sites): a draft in the editor belongs to
/// the session it was typed in. The in-place `/switch` stashes it for the
/// outgoing session and clears the editor (Enter after the switch submits
/// nothing), and a switch back restores it — the restored draft is a live
/// editor draft (Enter submits it, and only to the session it belongs to).
#[tokio::test]
async fn tui_prompt_stash_round_trips_across_in_place_switch() {
    use crossterm::event::{KeyCode, KeyEvent, KeyModifiers};

    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    let supervisor = spawn_supervisor(dir.path());
    let script = serde_json::json!({
        "engine": "faux",
        "responses": [{ "text": "stash switch reply", "delayMs": 10 }],
    });
    let script_path = dir.path().join("script.json");
    let first = create_session_via_daemon(
        &supervisor.socket,
        &script_path,
        &script,
        dir.path(),
        &session_dir,
    )
    .await;
    let second = create_session_via_daemon(
        &supervisor.socket,
        &script_path,
        &script,
        dir.path(),
        &session_dir,
    )
    .await;

    let options = eukhe_tui::interactive::InteractiveOptions {
        models: None,
        provider_auth: None,
        traces: None,
        socket_path: supervisor.socket.clone(),
        cwd: dir.path().to_path_buf(),
        session_dir: Some(session_dir.clone()),
        script_path: Some(script_path.clone()),
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
        client_settings: None,
        telemetry: None,
        keybindings: eukhe_tui::keybindings::KeybindingsManager::new(),
        prompt_stash: std::sync::Arc::default(),
        session_rlm_depth: None,
        session_has_children: false,
        restore_dock_focus: false,
    };
    let enter = || {
        eukhe_tui::interactive::HeadlessStep::Key(KeyEvent::new(KeyCode::Enter, KeyModifiers::NONE))
    };
    let plan = eukhe_tui::interactive::HeadlessPlan {
        steps: vec![
            // A draft for session A, never submitted.
            eukhe_tui::interactive::HeadlessStep::Type("f24 stash draft hello".to_string()),
            // The switch stashes the draft for A and clears the editor.
            eukhe_tui::interactive::HeadlessStep::Submit(format!("/switch {second}")),
            // The editor must be empty now: Enter submits nothing, and the
            // draft never bleeds into session B.
            enter(),
            eukhe_tui::interactive::HeadlessStep::WaitMs(500),
            // Switch back: the stashed draft returns to the editor.
            eukhe_tui::interactive::HeadlessStep::Submit(format!("/switch {first}")),
            // The restored draft is live: Enter submits it — to session A.
            enter(),
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
        rendered.contains("Restored stashed prompt"),
        "the switch-back restored the stashed draft:\n{rendered}"
    );

    // Daemon-side: the restored draft ran on session A, and session B
    // never received it (the editor cleared at the switch).
    let (client, _events) = eukhe_tui::daemon_client::DaemonClient::connect(&supervisor.socket)
        .await
        .expect("connect supervisor");
    let last_first = client
        .request_ok(DaemonCommand::GetLastAssistantText {
            id: None,
            active_session_id: first.clone(),
            rest: serde_json::Map::default(),
        })
        .await
        .expect("get_last_assistant_text on the first session");
    assert_eq!(
        last_first["text"], "stash switch reply",
        "the restored draft submitted to the session it belongs to"
    );
    let last_second = client
        .request_ok(DaemonCommand::GetLastAssistantText {
            id: None,
            active_session_id: second.clone(),
            rest: serde_json::Map::default(),
        })
        .await
        .expect("get_last_assistant_text on the second session");
    assert_eq!(
        last_second["text"],
        serde_json::Value::Null,
        "the stashed draft never leaked into the switched-to session"
    );
    client.close();
    drop(supervisor);
}

/// Prompt-stash verifier, the agents-view handoff arm: the (user-rebound)
/// `app.session.resume` key leaves for the agents view WITH a draft in the
/// editor — the draft is stashed for the session, and the chat that reopens
/// that session (the agents-view loop's next run, same process store)
/// restores it. The restored draft submits on Enter.
#[tokio::test]
async fn tui_prompt_stash_survives_the_agents_view_handoff() {
    use crossterm::event::{KeyCode, KeyEvent, KeyModifiers};

    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    // The keybindings fixture: `app.session.resume` has no default key, so
    // the fixture binds it to a plain key exactly like the TS parity flow
    // drives the same surface (both products fire the action while the
    // editor carries text).
    std::fs::write(
        agent_dir.join("keybindings.json"),
        r#"{ "app.session.resume": "f2" }"#,
    )
    .expect("write keybindings.json");
    let supervisor = spawn_supervisor(dir.path());
    let script = serde_json::json!({
        "engine": "faux",
        "responses": [{ "text": "handoff restore reply", "delayMs": 10 }],
    });
    let script_path = dir.path().join("script.json");
    let first = create_session_via_daemon(
        &supervisor.socket,
        &script_path,
        &script,
        dir.path(),
        &session_dir,
    )
    .await;

    // The clipboard seam fixture: the draft carries a pasted image, so the
    // handoff must round-trip the image bytes too (the reopened chat is a
    // fresh UI with an empty paste registry — the stash hydrates it).
    let png_path = dir.path().join("fixture.png");
    std::fs::write(&png_path, MINIMAL_PNG).expect("write fixture image");
    std::env::set_var("EUKHE_TEST_CLIPBOARD_IMAGE", &png_path);
    let prompt_stash: std::sync::Arc<std::sync::Mutex<eukhe_tui::prompt_stash::PromptStashStore>> =
        std::sync::Arc::default();
    let make_options = || eukhe_tui::interactive::InteractiveOptions {
        models: None,
        provider_auth: None,
        traces: None,
        socket_path: supervisor.socket.clone(),
        cwd: dir.path().to_path_buf(),
        session_dir: Some(session_dir.clone()),
        script_path: Some(script_path.clone()),
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
        client_settings: None,
        telemetry: None,
        keybindings: eukhe_tui::keybindings::KeybindingsManager::create(&agent_dir),
        prompt_stash: prompt_stash.clone(),
        session_rlm_depth: None,
        session_has_children: false,
        restore_dock_focus: false,
    };

    // Run one: the draft is typed, then the resume key hands the pane to
    // the agents view (the outcome eukhe-cli's agents-view loop consumes).
    let plan_one = eukhe_tui::interactive::HeadlessPlan {
        steps: vec![
            // The pasted image rides the draft into the stash.
            eukhe_tui::interactive::HeadlessStep::Key(KeyEvent::new(
                KeyCode::Char('v'),
                KeyModifiers::CONTROL,
            )),
            eukhe_tui::interactive::HeadlessStep::WaitMs(300),
            eukhe_tui::interactive::HeadlessStep::Type(" f24 handoff draft".to_string()),
            eukhe_tui::interactive::HeadlessStep::Key(KeyEvent::new(
                KeyCode::F(2),
                KeyModifiers::NONE,
            )),
        ],
        width: 100,
        height: 30,
    };
    let outcome_one = run_headless_bounded(make_options(), plan_one)
        .await
        .expect("interactive run one");
    assert!(
        outcome_one.return_to_agents_view,
        "the resume key hands the pane to the agents view"
    );

    // Run two (the agents view reopened the session): the same process
    // store restores the stashed draft into the fresh editor.
    let plan_two = eukhe_tui::interactive::HeadlessPlan {
        steps: vec![
            eukhe_tui::interactive::HeadlessStep::WaitMs(300),
            // The restored draft is live: Enter submits it.
            eukhe_tui::interactive::HeadlessStep::Key(KeyEvent::new(
                KeyCode::Enter,
                KeyModifiers::NONE,
            )),
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 30_000 },
        ],
        width: 100,
        height: 30,
    };
    let outcome_two = run_headless_bounded(make_options(), plan_two)
        .await
        .expect("interactive run two");
    let rendered = outcome_two.frames.join("\n");
    assert!(
        rendered.contains("Restored stashed prompt"),
        "the reopened chat restored the stashed draft:\n{rendered}"
    );
    assert!(
        rendered.contains("[image #1]"),
        "the restored draft carries its image marker:\n{rendered}"
    );

    // The persisted user message carries the image content: the fresh
    // chat's registry held the image only through the stash hydrate.
    let mut persisted_with_image = false;
    for entry in std::fs::read_dir(&session_dir)
        .expect("read session dir")
        .flatten()
    {
        let path = entry.path();
        if path.extension().and_then(|e| e.to_str()) == Some("jsonl") {
            if let Ok(text) = std::fs::read_to_string(&path) {
                persisted_with_image |= text.contains("image/png");
            }
        }
    }
    assert!(
        persisted_with_image,
        "the restored draft attached the stashed image bytes on submit"
    );

    // Daemon-side: the restored draft ran on the session.
    let (client, _events) = eukhe_tui::daemon_client::DaemonClient::connect(&supervisor.socket)
        .await
        .expect("connect supervisor");
    let last = client
        .request_ok(DaemonCommand::GetLastAssistantText {
            id: None,
            active_session_id: first.clone(),
            rest: serde_json::Map::default(),
        })
        .await
        .expect("get_last_assistant_text");
    assert_eq!(
        last["text"], "handoff restore reply",
        "the restored draft submitted after the handoff"
    );
    client.close();
    drop(supervisor);
}

/// Prompt-stash verifier, the pasted-image arm: the stashed draft carries
/// its pasted image. The clipboard seam fixture (`EUKHE_TEST_
/// CLIPBOARD_IMAGE`, the `script_path` verification-seam pattern) drives the
/// real paste path; the stash must round-trip the image bytes so the
/// restored draft's `[image #N]` marker attaches them on submit (the
/// persisted user message carries the image content).
#[tokio::test]
async fn tui_prompt_stash_restores_a_pasted_image_with_the_draft() {
    use crossterm::event::{KeyCode, KeyEvent, KeyModifiers};

    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    // A one-pixel PNG: the clipboard fixture stands in for the system
    // clipboard (this harness has no display server).
    let png_path = dir.path().join("fixture.png");
    std::fs::write(&png_path, MINIMAL_PNG).expect("write fixture image");
    // The seam only ever applies to the paste path (ctrl+v) — nothing else
    // in this binary reads the clipboard. The var stays set for the whole
    // test process: the parallel stash tests each reset it before their
    // own paste, so a cross-test remove would race them.
    std::env::set_var("EUKHE_TEST_CLIPBOARD_IMAGE", &png_path);
    let supervisor = spawn_supervisor(dir.path());
    let script = serde_json::json!({
        "engine": "faux",
        "responses": [{ "text": "image stash reply", "delayMs": 10 }],
    });
    let script_path = dir.path().join("script.json");
    let first = create_session_via_daemon(
        &supervisor.socket,
        &script_path,
        &script,
        dir.path(),
        &session_dir,
    )
    .await;
    let second = create_session_via_daemon(
        &supervisor.socket,
        &script_path,
        &script,
        dir.path(),
        &session_dir,
    )
    .await;

    let options = eukhe_tui::interactive::InteractiveOptions {
        models: None,
        provider_auth: None,
        traces: None,
        socket_path: supervisor.socket.clone(),
        cwd: dir.path().to_path_buf(),
        session_dir: Some(session_dir.clone()),
        script_path: Some(script_path.clone()),
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
        client_settings: None,
        telemetry: None,
        keybindings: eukhe_tui::keybindings::KeybindingsManager::new(),
        prompt_stash: std::sync::Arc::default(),
        session_rlm_depth: None,
        session_has_children: false,
        restore_dock_focus: false,
    };
    let ctrl_v = || {
        eukhe_tui::interactive::HeadlessStep::Key(KeyEvent::new(
            KeyCode::Char('v'),
            KeyModifiers::CONTROL,
        ))
    };
    let enter = || {
        eukhe_tui::interactive::HeadlessStep::Key(KeyEvent::new(KeyCode::Enter, KeyModifiers::NONE))
    };
    let plan = eukhe_tui::interactive::HeadlessPlan {
        steps: vec![
            // Paste an image (the seam fixture), then type around its
            // marker so the draft carries the marker.
            ctrl_v(),
            eukhe_tui::interactive::HeadlessStep::WaitMs(300),
            eukhe_tui::interactive::HeadlessStep::Type(" f24 image draft".to_string()),
            // Stash on switch, restore on switch back.
            eukhe_tui::interactive::HeadlessStep::Submit(format!("/switch {second}")),
            eukhe_tui::interactive::HeadlessStep::WaitMs(300),
            eukhe_tui::interactive::HeadlessStep::Submit(format!("/switch {first}")),
            eukhe_tui::interactive::HeadlessStep::WaitMs(300),
            // Submit the restored draft: the marker must resolve to the
            // stashed image bytes.
            enter(),
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
        rendered.contains("Restored stashed prompt"),
        "the switch-back restored the image draft:\n{rendered}"
    );
    assert!(
        rendered.contains("[image #1]"),
        "the restored draft carries its image marker:\n{rendered}"
    );
    // The persisted user message carries the image content: the restored
    // marker attached the stashed bytes on submit. The create response's
    // id is the active session id, so scan the session dir for the image
    // content (only session A received the draft).
    let mut persisted_with_image = String::new();
    for entry in std::fs::read_dir(&session_dir)
        .expect("read session dir")
        .flatten()
    {
        let path = entry.path();
        if path.extension().and_then(|e| e.to_str()) == Some("jsonl") {
            if let Ok(text) = std::fs::read_to_string(&path) {
                if text.contains("image/png") {
                    persisted_with_image = text;
                    break;
                }
            }
        }
    }
    assert!(
        !persisted_with_image.is_empty(),
        "the submitted restored draft attached the pasted image: no session file carries image content"
    );
    drop(supervisor);
}

/// TS `handlePromptStash` — the `app.prompt.stash` action on its DEFAULT
/// key (ctrl+s): with a draft in the editor the key stashes the whole
/// draft (text plus its pasted image) and the editor clears; with an
/// empty editor the key restores it — the restored draft is live, Enter
/// submits it, and the image marker resolves to the stashed bytes (the
/// same clipboard-seam machinery as the switch round-trip above).
#[tokio::test]
async fn tui_ctrl_s_stashes_and_restores_the_prompt_draft() {
    use crossterm::event::{KeyCode, KeyEvent, KeyModifiers};

    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    // The clipboard seam fixture: the draft carries a pasted image, so the
    // manual stash must round-trip the image bytes exactly like the auto
    // paths do (the var stays set for the whole test process, matching the
    // parallel stash tests' pattern).
    let png_path = dir.path().join("fixture.png");
    std::fs::write(&png_path, MINIMAL_PNG).expect("write fixture image");
    std::env::set_var("EUKHE_TEST_CLIPBOARD_IMAGE", &png_path);
    let supervisor = spawn_supervisor(dir.path());
    let script = serde_json::json!({
        "engine": "faux",
        "responses": [{ "text": "ctrl s stash reply", "delayMs": 10 }],
    });
    let script_path = dir.path().join("script.json");
    let session = create_session_via_daemon(
        &supervisor.socket,
        &script_path,
        &script,
        dir.path(),
        &session_dir,
    )
    .await;

    let options = eukhe_tui::interactive::InteractiveOptions {
        models: None,
        provider_auth: None,
        traces: None,
        socket_path: supervisor.socket.clone(),
        cwd: dir.path().to_path_buf(),
        session_dir: Some(session_dir.clone()),
        script_path: Some(script_path.clone()),
        model_selection: eukhe_tui::interactive::ModelSelection::default(),
        model_catalog: Vec::new(),
        model_configured_providers: std::collections::HashSet::default(),
        model_recent_models: Vec::new(),
        default_thinking_level: None,
        no_session: false,
        session: eukhe_tui::interactive::SessionSelection::Attach(session.clone()),
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
        client_settings: None,
        telemetry: None,
        keybindings: eukhe_tui::keybindings::KeybindingsManager::new(),
        prompt_stash: std::sync::Arc::default(),
        session_rlm_depth: None,
        session_has_children: false,
        restore_dock_focus: false,
    };
    let key = |code: KeyCode, modifiers: KeyModifiers| {
        eukhe_tui::interactive::HeadlessStep::Key(KeyEvent::new(code, modifiers))
    };
    let plan = eukhe_tui::interactive::HeadlessPlan {
        steps: vec![
            // A draft carrying a pasted image.
            key(KeyCode::Char('v'), KeyModifiers::CONTROL),
            eukhe_tui::interactive::HeadlessStep::WaitRender {
                needle: "[image #1]".to_string(),
                timeout_ms: 5_000,
            },
            eukhe_tui::interactive::HeadlessStep::Type(" f24 ctrl s draft".to_string()),
            // The manual stash: the status names it, the editor clears.
            key(KeyCode::Char('s'), KeyModifiers::CONTROL),
            eukhe_tui::interactive::HeadlessStep::WaitRender {
                needle: "Stashed prompt".to_string(),
                timeout_ms: 5_000,
            },
            // The editor is provably empty: Enter submits nothing (were the
            // draft still there, this submit would start its turn).
            key(KeyCode::Enter, KeyModifiers::NONE),
            eukhe_tui::interactive::HeadlessStep::WaitMs(400),
            // The restore: the draft (text and image marker) returns.
            key(KeyCode::Char('s'), KeyModifiers::CONTROL),
            eukhe_tui::interactive::HeadlessStep::WaitRender {
                needle: "Restored stashed prompt".to_string(),
                timeout_ms: 5_000,
            },
            // The restored draft is live: Enter submits it with its image.
            key(KeyCode::Enter, KeyModifiers::NONE),
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 30_000 },
        ],
        width: 100,
        height: 30,
    };
    let outcome = run_headless_bounded(options, plan)
        .await
        .expect("interactive run");
    let frames = &outcome.frames;
    let stash_index = frames
        .iter()
        .position(|frame| frame.contains("Stashed prompt"))
        .expect("the stash status rendered");
    let restore_index = frames
        .iter()
        .position(|frame| frame.contains("Restored stashed prompt"))
        .expect("the restore status rendered");
    assert!(stash_index < restore_index);
    // Between the stash and the restore the editor holds no draft: the
    // stash cleared it (the empty Enter between the two keys submitted
    // nothing, so the draft never became a user message either).
    for frame in &frames[stash_index..restore_index] {
        assert!(
            !frame.contains("f24 ctrl s draft"),
            "the stash cleared the editor:\n{frame}"
        );
    }
    // The restored draft carries its image marker again.
    assert!(
        frames[restore_index..]
            .iter()
            .any(|frame| frame.contains("[image #1]")),
        "the restored draft carries its image marker"
    );

    // Daemon-side: exactly the restored draft's turn ran (the empty
    // Enter submitted nothing), and its image bytes persisted.
    let (client, _events) = eukhe_tui::daemon_client::DaemonClient::connect(&supervisor.socket)
        .await
        .expect("connect supervisor");
    let last = client
        .request_ok(DaemonCommand::GetLastAssistantText {
            id: None,
            active_session_id: session.clone(),
            rest: serde_json::Map::default(),
        })
        .await
        .expect("get_last_assistant_text");
    assert_eq!(
        last["text"], "ctrl s stash reply",
        "the restored draft submitted after the manual round-trip"
    );
    client.close();
    let mut persisted_with_image = false;
    for entry in std::fs::read_dir(&session_dir)
        .expect("read session dir")
        .flatten()
    {
        let path = entry.path();
        if path.extension().and_then(|e| e.to_str()) == Some("jsonl") {
            if let Ok(text) = std::fs::read_to_string(&path) {
                persisted_with_image |= text.contains("image/png");
            }
        }
    }
    assert!(
        persisted_with_image,
        "the restored draft attached the stashed image bytes on submit"
    );
    drop(supervisor);
}

/// TS `handlePromptStash`'s two status guards: the key on an empty editor
/// with nothing stashed reports "No prompt to stash", and the key with a
/// draft while a stash is already held reports "Prompt stash already has
/// a draft" — the fresh draft STAYS in the editor (the manual stash never
/// clobbers a held one), submits on Enter, and the admitted send
/// restores the held draft into the emptied editor (TS
/// `promptStashToRestore`).
#[tokio::test]
async fn tui_ctrl_s_stash_keeps_a_held_draft_and_reports_the_empty_editor() {
    use crossterm::event::{KeyCode, KeyEvent, KeyModifiers};

    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    let supervisor = spawn_supervisor(dir.path());
    let script = serde_json::json!({
        "engine": "faux",
        "responses": [{ "text": "guard stash reply", "delayMs": 10 }],
    });
    let script_path = dir.path().join("script.json");
    let session = create_session_via_daemon(
        &supervisor.socket,
        &script_path,
        &script,
        dir.path(),
        &session_dir,
    )
    .await;

    let options = eukhe_tui::interactive::InteractiveOptions {
        models: None,
        provider_auth: None,
        traces: None,
        socket_path: supervisor.socket.clone(),
        cwd: dir.path().to_path_buf(),
        session_dir: Some(session_dir.clone()),
        script_path: Some(script_path.clone()),
        model_selection: eukhe_tui::interactive::ModelSelection::default(),
        model_catalog: Vec::new(),
        model_configured_providers: std::collections::HashSet::default(),
        model_recent_models: Vec::new(),
        default_thinking_level: None,
        no_session: false,
        session: eukhe_tui::interactive::SessionSelection::Attach(session.clone()),
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
        client_settings: None,
        telemetry: None,
        keybindings: eukhe_tui::keybindings::KeybindingsManager::new(),
        prompt_stash: std::sync::Arc::default(),
        session_rlm_depth: None,
        session_has_children: false,
        restore_dock_focus: false,
    };
    let key = |code: KeyCode, modifiers: KeyModifiers| {
        eukhe_tui::interactive::HeadlessStep::Key(KeyEvent::new(code, modifiers))
    };
    let plan = eukhe_tui::interactive::HeadlessPlan {
        steps: vec![
            // Empty editor, nothing stashed: the report, no restore.
            key(KeyCode::Char('s'), KeyModifiers::CONTROL),
            eukhe_tui::interactive::HeadlessStep::WaitRender {
                needle: "No prompt to stash".to_string(),
                timeout_ms: 5_000,
            },
            // A draft, then the stash that takes it.
            eukhe_tui::interactive::HeadlessStep::Type("f24 guard draft".to_string()),
            key(KeyCode::Char('s'), KeyModifiers::CONTROL),
            eukhe_tui::interactive::HeadlessStep::WaitRender {
                needle: "Stashed prompt".to_string(),
                timeout_ms: 5_000,
            },
            // A fresh draft while the stash holds one: the report, and
            // the fresh draft stays in the editor.
            eukhe_tui::interactive::HeadlessStep::Type("f24 second draft".to_string()),
            key(KeyCode::Char('s'), KeyModifiers::CONTROL),
            eukhe_tui::interactive::HeadlessStep::WaitRender {
                needle: "Prompt stash already has a draft".to_string(),
                timeout_ms: 5_000,
            },
            // The fresh draft stayed live: Enter submits it.
            key(KeyCode::Enter, KeyModifiers::NONE),
            // The admitted submit returns the held FIRST draft to the emptied
            // editor (TS `promptStashToRestore`, interactive-mode.ts:5752-5759).
            eukhe_tui::interactive::HeadlessStep::WaitRender {
                needle: "Restored stashed prompt".to_string(),
                timeout_ms: 5_000,
            },
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 30_000 },
        ],
        width: 100,
        height: 30,
    };
    let outcome = run_headless_bounded(options, plan)
        .await
        .expect("interactive run");
    let frames = &outcome.frames;
    // The already-held guard fired while the fresh draft sat in the
    // editor: from the guard's status onward the draft stays rendered
    // (it submits on the next Enter, so it also becomes the user row).
    let guard_index = frames
        .iter()
        .position(|frame| frame.contains("Prompt stash already has a draft"))
        .expect("the already-held status rendered");
    assert!(
        frames[guard_index].contains("f24 second draft"),
        "the fresh draft stayed in the editor at the guard:\n{}",
        frames[guard_index]
    );
    // The admitted send restored the held first draft into the editor.
    let restore_index = frames
        .iter()
        .position(|frame| frame.contains("Restored stashed prompt"))
        .expect("the restore status rendered");
    assert!(
        frames[restore_index..]
            .iter()
            .any(|frame| frame.contains("f24 guard draft")),
        "the admitted send restored the held draft into the editor"
    );

    // Daemon-side: the fresh draft submitted (it never left the editor).
    let (client, _events) = eukhe_tui::daemon_client::DaemonClient::connect(&supervisor.socket)
        .await
        .expect("connect supervisor");
    let last = client
        .request_ok(DaemonCommand::GetLastAssistantText {
            id: None,
            active_session_id: session.clone(),
            rest: serde_json::Map::default(),
        })
        .await
        .expect("get_last_assistant_text");
    assert_eq!(
        last["text"], "guard stash reply",
        "the fresh draft submitted while the stash held the first one"
    );
    client.close();
    drop(supervisor);
}

/// The `app.prompt.stash` action is remappable through
/// `keybindings.json` (the TS binding surface's contract): a user binding
/// replaces the default outright — ctrl+s goes inert (the draft stays in
/// the editor) and the user key stashes/restores instead.
#[tokio::test]
async fn tui_ctrl_s_stash_is_remappable_via_keybindings_json() {
    use crossterm::event::{KeyCode, KeyEvent, KeyModifiers};

    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    // The remap fixture: the action moves to f3, replacing ctrl+s.
    std::fs::write(
        agent_dir.join("keybindings.json"),
        r#"{ "app.prompt.stash": "f3" }"#,
    )
    .expect("write keybindings.json");
    let supervisor = spawn_supervisor(dir.path());
    let script = serde_json::json!({
        "engine": "faux",
        "responses": [{ "text": "remap stash reply", "delayMs": 10 }],
    });
    let script_path = dir.path().join("script.json");
    let session = create_session_via_daemon(
        &supervisor.socket,
        &script_path,
        &script,
        dir.path(),
        &session_dir,
    )
    .await;

    let options = eukhe_tui::interactive::InteractiveOptions {
        models: None,
        provider_auth: None,
        traces: None,
        socket_path: supervisor.socket.clone(),
        cwd: dir.path().to_path_buf(),
        session_dir: Some(session_dir.clone()),
        script_path: Some(script_path.clone()),
        model_selection: eukhe_tui::interactive::ModelSelection::default(),
        model_catalog: Vec::new(),
        model_configured_providers: std::collections::HashSet::default(),
        model_recent_models: Vec::new(),
        default_thinking_level: None,
        no_session: false,
        session: eukhe_tui::interactive::SessionSelection::Attach(session.clone()),
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
        client_settings: None,
        telemetry: None,
        keybindings: eukhe_tui::keybindings::KeybindingsManager::create(&agent_dir),
        prompt_stash: std::sync::Arc::default(),
        session_rlm_depth: None,
        session_has_children: false,
        restore_dock_focus: false,
    };
    let key = |code: KeyCode, modifiers: KeyModifiers| {
        eukhe_tui::interactive::HeadlessStep::Key(KeyEvent::new(code, modifiers))
    };
    let plan = eukhe_tui::interactive::HeadlessPlan {
        steps: vec![
            eukhe_tui::interactive::HeadlessStep::Type("f24 remap draft".to_string()),
            // The replaced default: ctrl+s no longer owns the action —
            // the draft stays in the editor.
            key(KeyCode::Char('s'), KeyModifiers::CONTROL),
            eukhe_tui::interactive::HeadlessStep::WaitMs(400),
            // The user key carries the action: the stash clears the editor.
            key(KeyCode::F(3), KeyModifiers::NONE),
            eukhe_tui::interactive::HeadlessStep::WaitRender {
                needle: "Stashed prompt".to_string(),
                timeout_ms: 5_000,
            },
            // And restores it.
            key(KeyCode::F(3), KeyModifiers::NONE),
            eukhe_tui::interactive::HeadlessStep::WaitRender {
                needle: "Restored stashed prompt".to_string(),
                timeout_ms: 5_000,
            },
            // The restored draft is live: Enter submits it.
            key(KeyCode::Enter, KeyModifiers::NONE),
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 30_000 },
        ],
        width: 100,
        height: 30,
    };
    let outcome = run_headless_bounded(options, plan)
        .await
        .expect("interactive run");
    let frames = &outcome.frames;
    let stash_index = frames
        .iter()
        .position(|frame| frame.contains("Stashed prompt"))
        .expect("the remapped key stashed");
    // The inertness proof: from the moment the full draft existed until
    // the remapped key stashed it, EVERY frame still shows the draft in
    // the editor — the ctrl+s press in that window did nothing.
    let full_draft_index = frames
        .iter()
        .position(|frame| frame.contains("f24 remap draft"))
        .expect("the draft rendered");
    assert!(full_draft_index < stash_index);
    for frame in &frames[full_draft_index..stash_index] {
        assert!(
            frame.contains("f24 remap draft"),
            "ctrl+s left the draft in the editor (the remap owns the action):\n{frame}"
        );
    }
    let restore_index = frames
        .iter()
        .position(|frame| frame.contains("Restored stashed prompt"))
        .expect("the remapped key restored");
    assert!(restore_index > stash_index);
    assert!(
        frames[restore_index..]
            .iter()
            .any(|frame| frame.contains("f24 remap draft")),
        "the restored draft returned to the editor"
    );

    // Daemon-side: the restored draft submitted.
    let (client, _events) = eukhe_tui::daemon_client::DaemonClient::connect(&supervisor.socket)
        .await
        .expect("connect supervisor");
    let last = client
        .request_ok(DaemonCommand::GetLastAssistantText {
            id: None,
            active_session_id: session.clone(),
            rest: serde_json::Map::default(),
        })
        .await
        .expect("get_last_assistant_text");
    assert_eq!(
        last["text"], "remap stash reply",
        "the restored draft submitted after the remap"
    );
    client.close();
    drop(supervisor);
}

/// Ctrl+s during a queue browse (Bugbot 79739005): the browse parks the
/// real draft in `queue_selection` and shows the selected parked
/// message's text in the editor, so the stash must leave the browse
/// first — like every other editor-mutating exit — and stash the
/// user's own draft, never the browsed parked text. The disarmed browse
/// also keeps the next Enter from applying an empty edit that would
/// DELETE the parked message.
#[tokio::test]
async fn tui_ctrl_s_during_queue_browse_stashes_the_draft_and_keeps_the_parked_message() {
    use crossterm::event::{KeyCode, KeyEvent, KeyModifiers};

    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    // The first turn holds for 8s: the whole queue dance (park two
    // prompts, draft, browse, stash, an empty Enter) runs inside the
    // busy window, deterministically.
    let supervisor = spawn_supervisor(dir.path());
    let script = serde_json::json!({
        "engine": "faux",
        "responses": [
            { "text": "the slow turn reply", "delayMs": 8000 },
            { "text": "steered delivery" },
            { "text": "followed up delivery" },
            { "text": "browse draft reply", "delayMs": 10 },
        ],
    });
    let script_path = dir.path().join("script.json");
    let session = create_session_via_daemon(
        &supervisor.socket,
        &script_path,
        &script,
        dir.path(),
        &session_dir,
    )
    .await;

    let options = eukhe_tui::interactive::InteractiveOptions {
        models: None,
        provider_auth: None,
        traces: None,
        socket_path: supervisor.socket.clone(),
        cwd: dir.path().to_path_buf(),
        session_dir: Some(session_dir.clone()),
        script_path: Some(script_path.clone()),
        model_selection: eukhe_tui::interactive::ModelSelection::default(),
        model_catalog: Vec::new(),
        model_configured_providers: std::collections::HashSet::default(),
        model_recent_models: Vec::new(),
        default_thinking_level: None,
        no_session: false,
        session: eukhe_tui::interactive::SessionSelection::Attach(session.clone()),
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
        client_settings: None,
        telemetry: None,
        keybindings: eukhe_tui::keybindings::KeybindingsManager::new(),
        prompt_stash: std::sync::Arc::default(),
        session_rlm_depth: None,
        session_has_children: false,
        restore_dock_focus: false,
    };
    let key = |code: KeyCode, modifiers: KeyModifiers| {
        eukhe_tui::interactive::HeadlessStep::Key(KeyEvent::new(code, modifiers))
    };
    let plan = eukhe_tui::interactive::HeadlessPlan {
        steps: vec![
            // The slow turn holds the run busy through the whole dance.
            eukhe_tui::interactive::HeadlessStep::Submit("start the slow turn".to_string()),
            eukhe_tui::interactive::HeadlessStep::WaitMs(750),
            // Two parked prompts: Enter while busy parks on the steering
            // lane, alt+Enter parks on the follow-up lane.
            eukhe_tui::interactive::HeadlessStep::Submit("steering prompt".to_string()),
            eukhe_tui::interactive::HeadlessStep::Type("follow-up prompt".to_string()),
            key(KeyCode::Enter, KeyModifiers::ALT),
            eukhe_tui::interactive::HeadlessStep::WaitRender {
                needle: "Follow-up: follow-up prompt".to_string(),
                timeout_ms: 5_000,
            },
            // A real draft, then the browse that parks it and loads the
            // newest parked message's text into the editor.
            eukhe_tui::interactive::HeadlessStep::Type("f24 browse draft".to_string()),
            eukhe_tui::interactive::HeadlessStep::WaitRender {
                needle: "f24 browse draft".to_string(),
                timeout_ms: 5_000,
            },
            key(KeyCode::Up, KeyModifiers::ALT),
            eukhe_tui::interactive::HeadlessStep::WaitRender {
                needle: "enter steers".to_string(),
                timeout_ms: 5_000,
            },
            // The stash: it leaves the browse (restoring the draft) and
            // stashes the draft — never the browsed parked text.
            key(KeyCode::Char('s'), KeyModifiers::CONTROL),
            eukhe_tui::interactive::HeadlessStep::WaitRender {
                needle: "Stashed prompt".to_string(),
                timeout_ms: 5_000,
            },
            // The empty-editor Enter with the browse disarmed submits
            // nothing: with the armed-browse bug this Enter would apply
            // an empty edit and DELETE the parked follow-up.
            key(KeyCode::Enter, KeyModifiers::NONE),
            // The run drains: the slow turn ends and both parked prompts
            // deliver (the follow-up's delivery IS the survival proof).
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 60_000 },
            // The stash held the pre-browse draft: the key restores it,
            // Enter submits it.
            key(KeyCode::Char('s'), KeyModifiers::CONTROL),
            eukhe_tui::interactive::HeadlessStep::WaitRender {
                needle: "Restored stashed prompt".to_string(),
                timeout_ms: 5_000,
            },
            key(KeyCode::Enter, KeyModifiers::NONE),
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 30_000 },
        ],
        width: 100,
        height: 30,
    };
    let outcome = run_headless_bounded(options, plan)
        .await
        .expect("interactive run");
    let frames = &outcome.frames;
    let browse_index = frames
        .iter()
        .position(|frame| frame.contains("enter steers"))
        .expect("the browse header rendered");
    let stash_index = frames
        .iter()
        .position(|frame| frame.contains("Stashed prompt"))
        .expect("the stash status rendered");
    assert!(browse_index < stash_index);
    // The browse ended with the stash: its header never renders again
    // (the armed browse is what would route the next Enter into a
    // queue edit).
    for frame in &frames[stash_index..] {
        assert!(
            !frame.contains("enter steers"),
            "the browse ended at the stash:\n{frame}"
        );
    }
    // Both parked prompts delivered after the turn: the stash + the
    // empty Enter deleted nothing, and nothing submitted early.
    let rendered = frames.join("\n");
    assert!(
        rendered.contains("steered delivery"),
        "the steering prompt delivered:\n{rendered}"
    );
    assert!(
        rendered.contains("followed up delivery"),
        "the parked follow-up survived the stash and the empty Enter:\n{rendered}"
    );
    // The stash held the pre-browse draft, not the browsed parked
    // text: the restore returns it.
    let restore_index = frames
        .iter()
        .position(|frame| frame.contains("Restored stashed prompt"))
        .expect("the restore status rendered");
    assert!(restore_index > stash_index);
    assert!(
        frames[restore_index..]
            .iter()
            .any(|frame| frame.contains("f24 browse draft")),
        "the restored draft is the pre-browse draft, not the parked text"
    );
    // Daemon-side: the restored draft's turn ran last.
    let (client, _events) = eukhe_tui::daemon_client::DaemonClient::connect(&supervisor.socket)
        .await
        .expect("connect supervisor");
    let last = client
        .request_ok(DaemonCommand::GetLastAssistantText {
            id: None,
            active_session_id: session.clone(),
            rest: serde_json::Map::default(),
        })
        .await
        .expect("get_last_assistant_text");
    assert_eq!(
        last["text"], "browse draft reply",
        "the restored draft submitted after the browse round-trip"
    );
    client.close();
    drop(supervisor);
}

/// The declared chat-editor keybindings dispatch (Phase A of the audit
/// table): ctrl+l opens the model picker, and the no-default-key actions
/// (`app.interrupt`, `app.session.new`) fire from a user keybindings.json.
/// Both were declared (ctrl+l also advertised in `/hotkeys`) without a
/// dispatch site on the base — the test fails there at the first render
/// barrier. ctrl+s's own dispatch landed upstream with its own e2e
/// (see `tui_ctrl_s_stashes_and_restores_the_prompt_draft`).
#[tokio::test]
async fn tui_dispatches_declared_editor_keybindings() {
    use crossterm::event::{KeyCode, KeyModifiers};

    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    std::fs::write(
        agent_dir.join("keybindings.json"),
        r#"{ "app.session.new": "ctrl+alt+n", "app.interrupt": "ctrl+alt+i" }"#,
    )
    .expect("write keybindings.json");
    let supervisor = spawn_supervisor(dir.path());
    // The second response keeps the turn alive on a visible marker while
    // the interrupt key lands (the pacing the menu-over-turn verifiers
    // use; the turn aborts long before its final answer).
    let script = serde_json::json!({
        "engine": "faux",
        "tokensPerSecond": 4,
        "responses": [
            { "text": "quick reply", "delayMs": 10 },
            { "content": [
                { "type": "text", "text": "the slow turn is streaming" },
                { "type": "thinking",
                  "thinking": "a long slow thinking pass keeps the turn alive while the interrupt key lands" },
                { "type": "text", "text": "the final answer that the abort must never deliver" },
            ] },
        ],
    });
    std::fs::write(dir.path().join("script.json"), script.to_string()).expect("write script");
    let mut options = base_options(&supervisor, dir.path(), &session_dir);
    // The exact load path the CLI uses: the fixture binds the two
    // no-default-key actions.
    options.keybindings = eukhe_tui::keybindings::KeybindingsManager::create(&agent_dir);
    let key = |code: KeyCode, modifiers: KeyModifiers| {
        eukhe_tui::interactive::HeadlessStep::Key(crossterm::event::KeyEvent::new(code, modifiers))
    };
    let wait_render = |needle: &str| eukhe_tui::interactive::HeadlessStep::WaitRender {
        needle: needle.to_string(),
        timeout_ms: 30_000,
    };
    let plan = eukhe_tui::interactive::HeadlessPlan {
        steps: vec![
            // The script's quick reply plays first so the slow turn below
            // streams while the interrupt key lands.
            eukhe_tui::interactive::HeadlessStep::Submit("hello".to_string()),
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 30_000 },
            // ctrl+l opens the /model surface.
            key(KeyCode::Char('l'), KeyModifiers::CONTROL),
            wait_render("Search models"),
            key(KeyCode::Esc, KeyModifiers::NONE),
            // The slow turn runs so the interrupt key lands mid-turn.
            eukhe_tui::interactive::HeadlessStep::Submit("start the slow turn".to_string()),
            wait_render("the slow turn is streaming"),
            key(
                KeyCode::Char('i'),
                KeyModifiers::CONTROL | KeyModifiers::ALT,
            ),
            wait_render("Press Ctrl+C again to exit"),
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 30_000 },
            // A draft in the editor when the new-session key lands: TS
            // `handleClearCommand` discards it (`resetCurrentSessionRenderState`),
            // it must not ride into the new session.
            eukhe_tui::interactive::HeadlessStep::Type("stale draft".to_string()),
            // The fixture binding runs the /new flow.
            key(
                KeyCode::Char('n'),
                KeyModifiers::CONTROL | KeyModifiers::ALT,
            ),
            wait_render("started session"),
        ],
        width: 120,
        height: 36,
    };
    let outcome = run_headless_bounded(options, plan)
        .await
        .expect("interactive run");
    let rendered = outcome.frames.join("\n");
    for status in ["Press Ctrl+C again to exit", "started session"] {
        assert!(
            rendered.contains(status),
            "the {status:?} row rendered:\n{rendered}"
        );
    }
    assert!(
        rendered.contains("Search models"),
        "ctrl+l opened the model picker:\n{rendered}"
    );
    assert!(
        !rendered.contains("the final answer that the abort must never deliver"),
        "the interrupt aborted the turn before its final answer:\n{rendered}"
    );
    // The new session started with no draft: the stale text the editor
    // held at the keypress never rendered into the new session's frames.
    let last = outcome.frames.last().expect("a final frame");
    assert!(
        !last.contains("stale draft"),
        "the new session discarded the editor draft:\n{last}"
    );
    drop(supervisor);
}
