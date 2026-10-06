//! Headless e2e for the chat turn wait: a turn queued behind another
//! window's turn on the shared chat shows `chat_turn_wait` as the loader
//! note while it waits, and the note goes once the wait ends; the
//! transcript never keeps it.
#![cfg(unix)]

use std::io::{BufRead, BufReader, Write};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::PathBuf;

use eukhe_tui::interactive::{
    run_interactive, HeadlessPlan, HeadlessStep, InteractiveOptions, ModelSelection,
    SessionSelection, UiMode,
};
use eukhe_types::daemon::CHAT_TURN_WAIT_NOTICE;
use serde_json::{json, Value};

/// One mock daemon: attaches mid-turn and reports the turn waiting; the
/// plan's `/name` rename is the cue that the wait ended (the lease was
/// granted), then the turn ends.
struct MockSupervisor {
    listener: UnixListener,
}

impl MockSupervisor {
    fn bind(socket: &std::path::Path) -> Self {
        MockSupervisor {
            listener: UnixListener::bind(socket).expect("bind mock socket"),
        }
    }

    /// Serve one client connection until it closes (bounded accept, so
    /// the plan teardown join always finishes).
    fn serve(self) {
        self.listener
            .set_nonblocking(true)
            .expect("nonblocking mock listener");
        let idle_until = std::time::Instant::now() + std::time::Duration::from_secs(10);
        let (stream, _) = loop {
            match self.listener.accept() {
                Ok(accepted) => break accepted,
                Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                    if std::time::Instant::now() >= idle_until {
                        return;
                    }
                    std::thread::sleep(std::time::Duration::from_millis(10));
                }
                Err(_) => return,
            }
        };
        stream
            .set_nonblocking(false)
            .expect("blocking mock connection");
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
            let command = envelope.get("command").cloned().unwrap_or(Value::Null);
            let command_type = command
                .get("type")
                .and_then(Value::as_str)
                .unwrap_or_default()
                .to_string();
            match command_type.as_str() {
                "create" => write_json(
                    &mut writer,
                    &json!({
                        "type": "response",
                        "id": id,
                        "command": "create",
                        "success": true,
                        "data": {
                            "activeSessionId": "s1",
                            "id": "s1",
                            "sessionId": "sess-1",
                            "sessionFile": "/tmp/sess-1.jsonl",
                        },
                    }),
                ),
                "attach" => {
                    write_json(&mut writer, &attach_data(id));
                    write_json(
                        &mut writer,
                        &session_event(&json!({
                            "type": "chat_turn_wait",
                            "waiting": true,
                        })),
                    );
                }
                "set_session_name" => {
                    write_json(&mut writer, &ok(id, &command_type));
                    write_json(
                        &mut writer,
                        &session_event(&json!({
                            "type": "chat_turn_wait",
                            "waiting": false,
                        })),
                    );
                    write_json(&mut writer, &session_event(&json!({ "type": "turn_end" })));
                }
                _ => write_json(&mut writer, &ok(id, &command_type)),
            }
        }
    }
}

fn ok(id: &str, command: &str) -> Value {
    json!({
        "type": "response",
        "id": id,
        "command": command,
        "success": true,
        "data": {},
    })
}

fn session_event(event: &Value) -> Value {
    json!({
        "type": "session_event",
        "activeSessionId": "s1",
        "event": event,
    })
}

fn write_json(writer: &mut UnixStream, value: &Value) {
    let mut line = serde_json::to_string(value).expect("serialize mock frame");
    line.push('\n');
    writer.write_all(line.as_bytes()).expect("write mock frame");
    writer.flush().expect("flush mock frame");
}

/// The attach result: a streaming mid-turn snapshot (the loader runs).
fn attach_data(id: &str) -> Value {
    let now_ms = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("clock after the epoch")
        .as_millis();
    json!({
        "type": "response",
        "id": id,
        "command": "attach",
        "success": true,
        "data": {
            "protocol": { "name": "eukhe.daemon", "version": 7 },
            "activeSessionId": "s1",
            "snapshot": {
                "activeSessionId": "s1",
                "summary": { "id": "s1", "cwd": "/tmp" },
                "state": {
                    "activeSessionId": "s1",
                    "cwd": "/tmp",
                    "sessionId": "sess-1",
                    "sessionName": "waiting session",
                    "model": null,
                    "isStreaming": true,
                    "isCompacting": false,
                    "sessionActions": { "queuedCount": 0, "steering": [], "followUps": [] },
                },
                "messages": [
                    {
                        "role": "user",
                        "content": [{ "type": "text", "text": "my turn next" }],
                        "timestamp": now_ms,
                    },
                ],
                "lastEventSequence": 0,
                "lastEventCursor": null,
            },
            "client": { "id": "mock", "capabilities": [] },
            "lastEventSequence": 0,
            "lastEventCursor": null,
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

#[test]
fn a_turn_waiting_for_another_windows_turn_shows_the_wait_until_it_ends() {
    // The ambient TMUX variable adds a startup notice to the
    // transcript; scrub it so the run is the same inside tmux and out.
    std::env::remove_var("TMUX");
    let dir = tempfile::TempDir::new().expect("temp dir");
    let socket = dir.path().join("tui.sock");
    let supervisor = MockSupervisor::bind(&socket);
    let handle = std::thread::spawn(move || supervisor.serve());
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .expect("tokio runtime");
    let plan = HeadlessPlan {
        steps: vec![
            HeadlessStep::WaitRender {
                needle: CHAT_TURN_WAIT_NOTICE.to_string(),
                timeout_ms: 10_000,
            },
            HeadlessStep::Submit("/name granted".to_string()),
            HeadlessStep::WaitGone {
                needle: CHAT_TURN_WAIT_NOTICE.to_string(),
                timeout_ms: 10_000,
            },
        ],
        width: 100,
        height: 40,
    };
    let outcome = runtime
        .block_on(run_interactive(options(socket), UiMode::Headless(plan)))
        .expect("interactive run");
    drop(runtime);
    handle.join().expect("mock supervisor finished");

    let shown = outcome
        .frames
        .iter()
        .position(|frame| frame.contains(CHAT_TURN_WAIT_NOTICE))
        .unwrap_or_else(|| panic!("the wait shows:\n{}", outcome.frames.join("\n---\n")));
    let last = outcome.frames.last().expect("a frame");
    assert!(
        !last.contains(CHAT_TURN_WAIT_NOTICE),
        "the wait clears and leaves no row (shown at frame {shown}):\n{last}"
    );
}
