//! Pane verifiers: session rename, the side-question pane, the settings
//! menu, and the completion menu's Esc.

use super::*;

/// `/name` and its `/rename` alias (TS `handleNameCommand`): the rename
/// travels to the daemon, the session storage persists the name (the
/// #188/#194 rename machinery), and the no-argument form reports the
/// current name.
#[tokio::test]
async fn tui_renames_session_through_slash_command() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    let supervisor = spawn_supervisor(dir.path());
    let script = serde_json::json!({ "engine": "faux", "responses": [
        { "text": "scripted reply" },
    ] });
    std::fs::write(dir.path().join("script.json"), script.to_string()).expect("write script");
    let options = base_options(&supervisor, dir.path(), &session_dir);
    let plan = eukhe_tui::interactive::HeadlessPlan {
        steps: vec![
            // Set through the alias: /rename resolves to /name.
            eukhe_tui::interactive::HeadlessStep::Submit("/rename my session".to_string()),
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 30_000 },
            // The no-argument form reports the current name.
            eukhe_tui::interactive::HeadlessStep::Submit("/name".to_string()),
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 30_000 },
        ],
        width: 120,
        height: 36,
    };
    let outcome = run_headless_bounded(options, plan)
        .await
        .expect("interactive run");
    let rendered = outcome.frames.join("\n");
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
    assert!(
        rendered.contains("Session name set: my session"),
        "the /rename status row rendered:\n{rendered}"
    );
    assert!(
        rendered.contains("Session name: my session"),
        "the /name report row rendered:\n{rendered}"
    );
    // The #188/#194 persistence: the session's storage carries the name
    // (the `eukhe.daemon.session` document the rename commits).
    assert!(
        session_dirs(&session_dir)
            .iter()
            .any(|storage| storage_contains(storage, "\"name\":\"my session\"")),
        "the session name persisted (the /name arm reaches the rename machinery)"
    );
    // The daemon state reports the name (the summary the roster and the
    // agents view read).
    let (client, _client_events) =
        eukhe_tui::daemon_client::DaemonClient::connect(&supervisor.socket)
            .await
            .expect("connect");
    let state = client
        .request_ok(DaemonCommand::GetState {
            id: None,
            active_session_id: outcome.active_session_id.clone(),
            rest: serde_json::Map::default(),
        })
        .await
        .expect("get_state");
    assert_eq!(state["sessionName"], "my session");
}

/// `/btw` (and its `/side` alias): the side-question pane mounts above the
/// dock, the daemon streams the answer, a reply follows up through the
/// pane, and Esc closes it.
#[tokio::test]
async fn tui_side_question_pane_flow() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    let supervisor = spawn_supervisor(dir.path());
    // Two scripted answers: the first /btw turn, then the follow-up reply.
    let script = serde_json::json!({ "engine": "faux", "responses": [
        { "text": "Paris, obviously" },
        { "text": "Second answer" },
    ] });
    std::fs::write(dir.path().join("script.json"), script.to_string()).expect("write script");
    let options = base_options(&supervisor, dir.path(), &session_dir);
    let escape = eukhe_tui::interactive::HeadlessStep::Key(crossterm::event::KeyEvent::new(
        crossterm::event::KeyCode::Esc,
        crossterm::event::KeyModifiers::NONE,
    ));
    let plan = eukhe_tui::interactive::HeadlessPlan {
        steps: vec![
            eukhe_tui::interactive::HeadlessStep::Submit(
                "/btw what is the capital of France".to_string(),
            ),
            // The side question runs outside the turn state (the WaitIdle
            // barrier cannot see it), and its answer is a daemon-driven
            // stream: wait for the rendered condition (early exit) instead
            // of a fixed wall-clock window.
            eukhe_tui::interactive::HeadlessStep::WaitRender {
                needle: "Paris, obviously".to_string(),
                timeout_ms: 30_000,
            },
            // The pane's run must SETTLE before the follow-up: TS's
            // active-run guard drops a follow-up submitted while the run
            // is still streaming (it keeps the draft and warns). The
            // settled hint row ("reply to follow up") is the pane's own
            // idle marker, so wait for it — never a fixed window.
            eukhe_tui::interactive::HeadlessStep::WaitRender {
                needle: "reply to follow up".to_string(),
                timeout_ms: 30_000,
            },
            eukhe_tui::interactive::HeadlessStep::SettleIdle,
            // The open pane captures a plain reply as a follow-up side
            // question (TS's side-conversation ladder).
            eukhe_tui::interactive::HeadlessStep::Submit("and its largest city".to_string()),
            eukhe_tui::interactive::HeadlessStep::WaitRender {
                needle: "Second answer".to_string(),
                timeout_ms: 30_000,
            },
            // Settle again: an Esc against a still-running pane would
            // CANCEL the run instead of closing the pane (TS's two-stage
            // escape), so the close step needs the pane idle too.
            eukhe_tui::interactive::HeadlessStep::WaitRender {
                needle: "reply to follow up".to_string(),
                timeout_ms: 30_000,
            },
            eukhe_tui::interactive::HeadlessStep::SettleIdle,
            // A slash command inside the pane gets the TS notice turn.
            eukhe_tui::interactive::HeadlessStep::Submit("/model".to_string()),
            eukhe_tui::interactive::HeadlessStep::WaitRender {
                needle: "Slash commands are not available in side conversations.".to_string(),
                timeout_ms: 30_000,
            },
            eukhe_tui::interactive::HeadlessStep::SettleIdle,
            // Esc returns to the main thread: the pane's hint row is the
            // surface's own state, so wait for it to leave the newest
            // frame.
            escape,
            eukhe_tui::interactive::HeadlessStep::WaitGone {
                needle: "esc to return to session".to_string(),
                timeout_ms: 10_000,
            },
            eukhe_tui::interactive::HeadlessStep::SettleIdle,
        ],
        width: 120,
        height: 36,
    };
    let outcome = run_headless_bounded(options, plan)
        .await
        .expect("interactive run");
    let rendered = outcome.frames.join("\n");
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
    assert!(
        rendered.contains("/btw  what is the capital of France"),
        "the pane rendered the /btw header:\n{rendered}"
    );
    assert!(
        rendered.contains("Paris, obviously"),
        "the streamed answer rendered in the pane:\n{rendered}"
    );
    // The follow-up renders as a user-message bubble (TS `questionBubble`).
    assert!(
        rendered.contains("and its largest city"),
        "the follow-up question rendered:\n{rendered}"
    );
    assert!(
        rendered.contains("Second answer"),
        "the follow-up answer rendered:\n{rendered}"
    );
    assert!(
        rendered.contains(
            "Slash commands are not available in side conversations. Press esc to return to the main thread."
        ),
        "the in-pane slash notice rendered:\n{rendered}"
    );
    assert!(
        rendered.contains("reply to follow up - esc to return to session"),
        "the pane hint rendered:\n{rendered}"
    );
    // Esc closed the pane: the final frame shows no pane rows.
    let last = outcome.frames.last().expect("a final frame");
    assert!(
        !last.contains("esc to return to session"),
        "esc closed the pane:\n{last}"
    );
    // The side turns never reached the session transcript (TS: side
    // questions are not durable): the session file has no side-question
    // user rows.
    let mut leaked = false;
    for entry in std::fs::read_dir(&session_dir)
        .expect("read session dir")
        .flatten()
    {
        let path = entry.path();
        if path.extension().and_then(|e| e.to_str()) != Some("jsonl") {
            continue;
        }
        let content = std::fs::read_to_string(&path).unwrap_or_default();
        leaked |= content.contains("what is the capital of France");
    }
    assert!(!leaked, "the side question stayed out of the session file");
}

/// `/settings` (TS `showSettingsSelector`): the menu mounts in the dock
/// and the settings rows cycle through the daemon switch.
#[tokio::test]
async fn tui_settings_menu_cycles_rows() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    let supervisor = spawn_supervisor(dir.path());
    let script = serde_json::json!({ "engine": "faux", "responses": [] });
    std::fs::write(dir.path().join("script.json"), script.to_string()).expect("write script");
    let options = base_options(&supervisor, dir.path(), &session_dir);
    let enter = || {
        eukhe_tui::interactive::HeadlessStep::Key(crossterm::event::KeyEvent::new(
            crossterm::event::KeyCode::Enter,
            crossterm::event::KeyModifiers::NONE,
        ))
    };
    let escape = || {
        eukhe_tui::interactive::HeadlessStep::Key(crossterm::event::KeyEvent::new(
            crossterm::event::KeyCode::Esc,
            crossterm::event::KeyModifiers::NONE,
        ))
    };
    let plan = eukhe_tui::interactive::HeadlessPlan {
        steps: vec![
            eukhe_tui::interactive::HeadlessStep::Submit("/settings".to_string()),
            eukhe_tui::interactive::HeadlessStep::WaitMs(500),
            eukhe_tui::interactive::HeadlessStep::SettleIdle,
            // Enter on the first row (Auto-compact) cycles it to false —
            // the daemon `set_auto_compaction` switch.
            enter(),
            eukhe_tui::interactive::HeadlessStep::WaitMs(500),
            eukhe_tui::interactive::HeadlessStep::SettleIdle,
            escape(),
            eukhe_tui::interactive::HeadlessStep::WaitMs(300),
        ],
        width: 120,
        height: 36,
    };
    let outcome = run_headless_bounded(options, plan)
        .await
        .expect("interactive run");
    let rendered = outcome.frames.join("\n");
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
    assert!(
        rendered.contains("Auto-compact"),
        "the settings menu rendered its first row:\n{rendered}"
    );
    assert!(
        rendered
            .contains("1 General    2 Models    3 Display    4 Terminal    5 Editor    6 Agents"),
        "the settings menu rendered its tab strip:\n{rendered}"
    );
    assert!(
        rendered
            .contains("Type to search - Tab/1-6 tabs - left/right/Enter/Space change - Esc close"),
        "the settings hint rendered:\n{rendered}"
    );
}

/// The operator's Esc-ordering pin (2026-09-25): while a turn streams, the
/// cwd completion menu (`./` + Tab) lists the non-hidden entries only (the
/// `.claude` directory stays out of the menu), and Esc closes the menu
/// without interrupting the running turn — the abort ladder runs only when
/// no menu is open.
#[tokio::test]
async fn tui_esc_closes_the_completion_menu_without_interrupting_the_turn() {
    use crossterm::event::KeyCode;

    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    std::fs::create_dir_all(dir.path().join(".claude")).expect("dot dir");
    std::fs::write(dir.path().join("main.rs"), "fn main() {}").expect("write");
    std::fs::write(dir.path().join("notes.md"), "notes").expect("write");
    // One turn: a fast text block marks it provably streaming, then the
    // slow thinking block keeps it alive while the menu interaction runs.
    let script = serde_json::json!({
        "engine": "faux",
        "tokensPerSecond": 4,
        "responses": [
            { "content": [
                { "type": "text", "text": "the turn is streaming" },
                { "type": "thinking",
                  "thinking": "a long slow thinking pass keeps the turn streaming while the completion menu opens and escape closes it" },
                { "type": "text", "text": "the final answer streams after the menu check" },
            ] },
        ],
    });
    std::fs::write(dir.path().join("script.json"), script.to_string()).expect("write script");
    let supervisor = spawn_supervisor(dir.path());
    let options = base_options(&supervisor, dir.path(), &session_dir);
    let key = |code: KeyCode| {
        eukhe_tui::interactive::HeadlessStep::Key(crossterm::event::KeyEvent::new(
            code,
            crossterm::event::KeyModifiers::NONE,
        ))
    };
    let plan = eukhe_tui::interactive::HeadlessPlan {
        steps: vec![
            eukhe_tui::interactive::HeadlessStep::Submit("start the long turn".to_string()),
            eukhe_tui::interactive::HeadlessStep::WaitRender {
                needle: "the turn is streaming".to_string(),
                timeout_ms: 30_000,
            },
            // The editor stays live during the turn: `./` + Tab opens the
            // cwd completion menu over it.
            eukhe_tui::interactive::HeadlessStep::Type("./".to_string()),
            key(KeyCode::Tab),
            eukhe_tui::interactive::HeadlessStep::SettleIdle,
            eukhe_tui::interactive::HeadlessStep::WaitRender {
                needle: "notes.md".to_string(),
                timeout_ms: 30_000,
            },
            // Esc closes the menu; the turn keeps running to its final
            // answer (a leaked abort would kill it mid-stream).
            key(KeyCode::Esc),
            eukhe_tui::interactive::HeadlessStep::WaitGone {
                needle: "notes.md".to_string(),
                timeout_ms: 10_000,
            },
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 60_000 },
        ],
        width: 100,
        height: 34,
    };
    let outcome = run_headless_bounded(options, plan)
        .await
        .expect("interactive run");
    let rendered = outcome.frames.join("\n");
    // The menu listed the cwd's non-hidden entries and never the dot dir.
    assert!(
        rendered.contains("main.rs") && rendered.contains("notes.md"),
        "the cwd completion menu listed the non-hidden entries:\n{rendered}"
    );
    assert!(
        !rendered.contains(".claude"),
        "the dot dir never lists in the cwd browse:\n{rendered}"
    );
    assert!(
        rendered.contains("the final answer streams after the menu check"),
        "Esc closed the menu and the turn ran to its final answer (no leaked abort):\n{rendered}"
    );
    drop(supervisor);
}
