//! Headless e2e for the terminal session-close rows: a session the daemon
//! killed, shut down, or replaced shows a persistent error row (TS
//! `showError`), not a replaceable note, so a later status note (the
//! cancelled turn's, any command's) never overwrites it.
#![cfg(unix)]

use std::io::{BufRead, BufReader, Write};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::PathBuf;

use eukhe_tui::interactive::{
    run_interactive, HeadlessPlan, HeadlessStep, InteractiveOptions, ModelSelection,
    SessionSelection, UiMode,
};
use serde_json::{json, Value};

const BARRIER_TIMEOUT_MS: u64 = 5000;

/// Serve one client: attach answers with an empty session, then the turn
/// starts and the session closes with `reason`; every other command gets
/// one success response.
fn serve(listener: &UnixListener, reason: &str) {
    let (stream, _) = listener.accept().expect("accept");
    let mut writer = stream.try_clone().expect("clone mock socket");
    let mut reader = BufReader::new(stream);
    write_json(
        &mut writer,
        &json!({
            "type": "daemon_hello",
            "protocol": { "name": "eukhe.daemon", "version": 7 },
            "serverCapabilities": [],
            "clientId": "mock",
        }),
    );
    let mut line = String::new();
    loop {
        line.clear();
        match reader.read_line(&mut line) {
            Ok(0) | Err(_) => break,
            Ok(_) => {}
        }
        let Ok(envelope) = serde_json::from_str::<Value>(line.trim()) else {
            continue;
        };
        let id = envelope.get("id").and_then(Value::as_str).unwrap_or("");
        let command_type = envelope
            .get("command")
            .and_then(|command| command.get("type"))
            .and_then(Value::as_str)
            .unwrap_or_default()
            .to_string();
        if command_type == "attach" {
            write_json(&mut writer, &attach_data(id));
            write_json(
                &mut writer,
                &json!({
                    "type": "session_event",
                    "activeSessionId": "s1",
                    "event": { "type": "turn_start" },
                }),
            );
            write_json(
                &mut writer,
                &json!({
                    "type": "session_closed",
                    "activeSessionId": "s1",
                    "reason": reason,
                }),
            );
            continue;
        }
        write_json(
            &mut writer,
            &json!({
                "type": "response",
                "id": id,
                "command": command_type,
                "success": true,
                "data": {
                    "activeSessionId": "s1",
                    "id": "s1",
                    "sessionId": "sess-1",
                    "sessionFile": "/tmp/sess-1.jsonl",
                },
            }),
        );
    }
}

fn write_json(writer: &mut UnixStream, value: &Value) {
    let mut line = serde_json::to_string(value).expect("serialize mock frame");
    line.push('\n');
    writer.write_all(line.as_bytes()).expect("write mock frame");
    writer.flush().expect("flush mock frame");
}

fn attach_data(id: &str) -> Value {
    json!({
        "type": "response",
        "id": id,
        "command": "attach",
        "success": true,
        "data": {
            "activeSessionId": "s1",
            "snapshot": {
                "state": {
                    "sessionId": "sess-1",
                    "sessionName": "closing session",
                    "isStreaming": false,
                },
                "messages": [],
            },
        },
    })
}

fn options(socket: PathBuf) -> InteractiveOptions {
    InteractiveOptions {
        models: None,
        socket_path: socket,
        cwd: PathBuf::from("/tmp"),
        session_dir: None,
        script_path: None,
        model_selection: ModelSelection::default(),
        model_catalog: Vec::new(),
        model_configured_providers: std::collections::HashSet::default(),
        model_recent_models: Vec::new(),
        default_thinking_level: None,
        no_session: false,
        session: SessionSelection::New,
        initial_message: None,
        show_images: true,
        screen_mode: eukhe_tui::screen_mode::ScreenMode::Inline,
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
    }
}

/// Close the session with `reason`, then let a later status note land; the
/// final frame must still carry the error row.
fn assert_close_error_survives_a_later_note(reason: &'static str, explanation: &str) {
    // The ambient TMUX variable adds a startup notice; scrub it.
    std::env::remove_var("TMUX");
    let dir = tempfile::TempDir::new().expect("temp dir");
    let socket = dir.path().join("tui.sock");
    let listener = UnixListener::bind(&socket).expect("bind mock socket");
    let handle = std::thread::spawn(move || serve(&listener, reason));
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .expect("tokio runtime");
    let error_row = format!("Error: {explanation}");
    let plan = HeadlessPlan {
        steps: vec![
            HeadlessStep::WaitRender {
                needle: error_row.clone(),
                timeout_ms: BARRIER_TIMEOUT_MS,
            },
            // A later status note: it rewrites the newest note row in place,
            // which used to be the `session closed (<reason>)` note.
            HeadlessStep::Submit("/name".to_string()),
            HeadlessStep::WaitRender {
                needle: "Session name: closing session".to_string(),
                timeout_ms: BARRIER_TIMEOUT_MS,
            },
        ],
        width: 260,
        height: 30,
    };
    let outcome = runtime
        .block_on(run_interactive(options(socket), UiMode::Headless(plan)))
        .expect("interactive run");
    handle.join().expect("mock supervisor finished");
    let all = outcome.frames.join("\n");
    assert!(
        !all.contains("timed out waiting"),
        "{reason}: a render barrier timed out:\n{all}"
    );
    let last = outcome.frames.last().expect("final frame");
    assert!(
        last.contains(&error_row) && last.contains("Session name: closing session"),
        "{reason}: the close error row must persist after a later note:\n{last}"
    );
}

#[test]
fn a_killed_session_keeps_its_error_row() {
    assert_close_error_survives_a_later_note(
        "killed",
        "The daemon stopped this agent session. Its transcript remains saved and can be reopened from Agents View.",
    );
}

#[test]
fn a_shut_down_session_keeps_its_error_row() {
    assert_close_error_survives_a_later_note(
        "shutdown",
        "The Eukhe daemon shut down while this window was attached. The session transcript remains saved; restart Eukhe and reopen it from Agents View.",
    );
}

#[test]
fn a_replaced_session_keeps_its_error_row() {
    assert_close_error_survives_a_later_note(
        "replaced",
        "The daemon replaced this agent session with another session. Reopen the current session from Agents View.",
    );
}
