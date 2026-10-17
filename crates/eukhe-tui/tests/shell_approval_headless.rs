//! Headless e2e for the `bash` step questions: a `shell_approval` frame
//! opens the yes/no confirm, a second one queues behind it, `Yes` answers
//! `approve`, escape answers `deny`, and the answers go out in order.
#![cfg(unix)]

use std::io::{BufRead, BufReader, Write};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::PathBuf;

use crossterm::event::{KeyCode, KeyEvent, KeyModifiers};
use eukhe_tui::interactive::{
    run_interactive, HeadlessPlan, HeadlessStep, InteractiveOptions, ModelSelection,
    SessionSelection, UiMode,
};
use eukhe_types::daemon::DaemonCommand;
use eukhe_types::shell::ShellVerdict;
use serde_json::{json, Map, Value};

const BARRIER_TIMEOUT_MS: u64 = 5000;

/// Serve one client: attach answers with an empty session and asks two
/// step questions; every command gets one success response. Returns the
/// `answer_shell_approval` commands the client sent.
fn serve(listener: &UnixListener) -> Vec<DaemonCommand> {
    let (stream, _) = listener.accept().expect("accept");
    let mut writer = stream.try_clone().expect("clone mock socket");
    let mut reader = BufReader::new(stream);
    write_json(
        &mut writer,
        &json!({
            "type": "daemon_hello",
            "protocol": { "name": "eukhe.daemon", "version": 7 },
            "serverCapabilities": ["shell_approval"],
            "clientId": "mock",
        }),
    );
    let mut answers = Vec::new();
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
        let command = envelope.get("command").cloned().unwrap_or(Value::Null);
        let command_type = command
            .get("type")
            .and_then(Value::as_str)
            .unwrap_or_default()
            .to_string();
        if command_type == "attach" {
            write_json(&mut writer, &attach_data(id));
            for (request_id, step, command) in [("r1", 0, "rm -rf build"), ("r2", 1, "curl x")] {
                write_json(
                    &mut writer,
                    &json!({
                        "type": "shell_approval",
                        "activeSessionId": "s1",
                        "request": {
                            "requestId": request_id,
                            "step": step,
                            "command": command,
                            "effect": "write",
                        },
                    }),
                );
            }
            continue;
        }
        if command_type == "answer_shell_approval" {
            answers.push(serde_json::from_value(command).expect("answer command"));
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
    answers
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
                "activeSessionId": "s1",
                "summary": { "id": "s1", "cwd": "/tmp" },
                "state": {
                    "sessionId": "sess-1",
                    "sessionName": "shell session",
                    "isStreaming": false,
                },
                "messages": [],
                "lastEventSequence": 0,
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
        client_auth: None,
        provider_auth: None,
        keybindings: eukhe_tui::keybindings::KeybindingsManager::new(),
        session_rlm_depth: None,
        prompt_stash: std::sync::Arc::default(),
        session_has_children: false,
        restore_dock_focus: false,
        client_settings: None,
    }
}

fn key(code: KeyCode) -> HeadlessStep {
    HeadlessStep::Key(KeyEvent::new(code, KeyModifiers::NONE))
}

fn answer(request_id: &str, verdict: ShellVerdict) -> DaemonCommand {
    DaemonCommand::AnswerShellApproval {
        id: None,
        active_session_id: "s1".to_string(),
        request_id: request_id.to_string(),
        verdict,
        rest: Map::default(),
    }
}

#[test]
fn step_questions_open_in_order_and_answer_the_daemon() {
    // The ambient TMUX variable adds a startup notice; scrub it.
    std::env::remove_var("TMUX");
    let dir = tempfile::TempDir::new().expect("temp dir");
    let socket = dir.path().join("tui.sock");
    let listener = UnixListener::bind(&socket).expect("bind mock socket");
    let handle = std::thread::spawn(move || serve(&listener));
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .expect("tokio runtime");
    let plan = HeadlessPlan {
        steps: vec![
            HeadlessStep::WaitRender {
                needle: "Allow shell step 0?".to_string(),
                timeout_ms: BARRIER_TIMEOUT_MS,
            },
            key(KeyCode::Enter),
            HeadlessStep::WaitRender {
                needle: "Allow shell step 1?".to_string(),
                timeout_ms: BARRIER_TIMEOUT_MS,
            },
            key(KeyCode::Esc),
            HeadlessStep::WaitGone {
                needle: "Allow shell step 1?".to_string(),
                timeout_ms: BARRIER_TIMEOUT_MS,
            },
        ],
        width: 200,
        height: 30,
    };
    let outcome = runtime
        .block_on(run_interactive(options(socket), UiMode::Headless(plan)))
        .expect("interactive run");
    let answers = handle.join().expect("mock supervisor finished");
    let all = outcome.frames.join("\n");
    assert!(
        !all.contains("timed out waiting"),
        "a render barrier timed out:\n{all}"
    );
    assert!(all.contains("write: rm -rf build"), "{all}");
    assert_eq!(
        answers,
        vec![
            answer("r1", ShellVerdict::Approve),
            answer("r2", ShellVerdict::Deny),
        ]
    );
}
