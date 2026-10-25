//! Headless e2e for the worker pane (docs/interface.md, "Worker pane"):
//! main's roster row lists a running worker, the client watch-attaches it
//! on the same connection and shows its stream beside main's chat (the
//! forwarded context row with the user's words, the streamed text, the
//! running tool); Shift+Alt+W opens the full view and Esc returns; Esc Esc
//! pauses the worker (`pause_workers`), the pane and the pinned block say
//! `paused`; Alt+W hides the pane.
#![cfg(unix)]
// - the futures are bounded by the surface's lifetime; boxing them would
//   add an allocation to the steady-state loop.
#![allow(clippy::large_futures)]

use std::io::{BufRead, BufReader, Write};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::PathBuf;

use crossterm::event::{KeyCode, KeyEvent, KeyModifiers};
use eukhe_tui::interactive::{
    run_interactive, HeadlessPlan, HeadlessStep, InteractiveOptions, ModelSelection,
    SessionSelection, UiMode,
};
use serde_json::{json, Value};

fn write_json(writer: &mut UnixStream, value: &Value) {
    let mut line = serde_json::to_string(value).expect("serialize mock frame");
    line.push('\n');
    writer.write_all(line.as_bytes()).expect("write mock frame");
    writer.flush().expect("flush mock frame");
}

fn worker_row(state: &str) -> Value {
    json!({ "activeSessionId": "w1", "sessionId": "w-sess", "name": "worker", "state": state })
}

/// Main's row (listing its worker in `state`), then the worker's own row.
fn roster(state: &str) -> Value {
    json!([
        {
            "agentId": "s1",
            "status": "idle",
            "summary": {
                "sessionId": "sess-1",
                "activeSessionId": "s1",
                "sessionName": "lead",
                "runtimeKind": "top-level",
                "workers": [worker_row(state)],
            },
        },
        {
            "agentId": "w1",
            "status": if state == "running" { "running" } else { "idle" },
            "summary": {
                "sessionId": "w-sess",
                "activeSessionId": "w1",
                "sessionName": "worker",
                "runtimeKind": "subagent",
                "rlmChildId": "sub-w1",
                "rlmDepth": 1,
                "parentActiveSessionId": "s1",
                "parentSessionId": "sess-1",
                "isStreaming": state == "running",
                "isPaused": state == "paused",
            },
        },
    ])
}

fn attach_data(id: &str, session: &str, messages: &Value) -> Value {
    json!({
        "protocol": { "name": "eukhe.daemon", "version": 7 },
        "activeSessionId": id,
        "snapshot": {
            "activeSessionId": id,
            "summary": { "id": id, "cwd": "/tmp" },
            "state": {
                "activeSessionId": id,
                "cwd": "/tmp",
                "sessionId": session,
                "model": "faux-1",
                "isStreaming": id == "w1",
                "isCompacting": false,
                "sessionActions": { "queuedCount": 0, "steering": [], "followUps": [] },
            },
            "messages": messages,
            "lastEventSequence": 2,
            "lastEventCursor": null,
        },
        "client": { "id": "mock", "capabilities": [] },
        "lastEventSequence": 2,
        "lastEventCursor": null,
    })
}

fn assistant(content: &Value) -> Value {
    json!({
        "role": "assistant",
        "content": content,
        "api": "scripted",
        "provider": "scripted",
        "model": "faux-1",
        "usage": {
            "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 0,
            "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
        },
        "stopReason": "toolUse",
        "timestamp": 3,
    })
}

/// The worker's live stream after the watch attach: a replayed frame the
/// snapshot holds, the forwarded context row, the streamed text, the
/// running tool.
fn stream_worker(writer: &mut UnixStream) {
    let event = |sequence: u64, payload: Value| json!({ "type": "session_event", "activeSessionId": "w1", "event": payload, "meta": { "sequence": sequence } });
    let frames = [
        event(
            2,
            json!({ "type": "message_start", "message": { "role": "user", "content": "replayed prompt", "timestamp": 1 } }),
        ),
        event(
            3,
            json!({
                "type": "message_start",
                "message": {
                    "role": "custom",
                    "customType": "agent_message",
                    "content": "[context from user via main]\n\nuse the v2 api",
                    "display": true,
                    "details": {
                        "deliveryKind": "context",
                        "userMessages": [{ "text": "use the v2 api" }],
                        "note": "asked mid-run",
                        "from": { "sessionName": "lead" },
                    },
                    "timestamp": 2,
                },
            }),
        ),
        event(
            4,
            json!({
                "type": "message_start",
                "message": assistant(&json!([{ "type": "text", "text": "Folding in the context" }])),
                "assistantMessageEvent": { "type": "start" },
            }),
        ),
        event(
            5,
            json!({
                "type": "message_end",
                "message": assistant(&json!([
                    { "type": "text", "text": "Folding in the context" },
                    { "type": "toolCall", "id": "t1", "name": "read", "arguments": { "path": "src/api.rs" } },
                ])),
            }),
        ),
        event(
            6,
            json!({ "type": "tool_execution_start", "toolCallId": "t1", "toolName": "read", "args": { "path": "src/api.rs" } }),
        ),
    ];
    for frame in &frames {
        write_json(writer, frame);
    }
}

/// Serve one connection; answers what the client asked, in order, as
/// `type` or `type:activeSessionId:clientKind`.
fn serve(listener: &UnixListener) -> Vec<String> {
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
    let mut asked = Vec::new();
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
        let command = &envelope["command"];
        let command_type = command["type"].as_str().unwrap_or_default().to_string();
        let target = command["activeSessionId"].as_str().unwrap_or_default();
        let data = match (command_type.as_str(), target) {
            ("attach", "w1") => {
                asked.push(format!(
                    "attach:w1:{}",
                    command["clientKind"].as_str().unwrap_or("interactive")
                ));
                attach_data(
                    "w1",
                    "w-sess",
                    &json!([{ "role": "user", "content": "replayed prompt", "timestamp": 1 }]),
                )
            }
            ("attach", _) => attach_data(
                "s1",
                "sess-1",
                &json!([{ "role": "user", "content": "hello main", "timestamp": 1 }]),
            ),
            ("roster_subscribe", _) => json!({ "roster": roster("running") }),
            ("pause_workers", _) => {
                asked.push(format!("pause_workers:{target}"));
                json!({ "workers": [worker_row("paused")] })
            }
            _ => json!({}),
        };
        write_json(
            &mut writer,
            &json!({
                "type": "response",
                "id": id,
                "command": command_type,
                "success": true,
                "data": data,
            }),
        );
        match (command_type.as_str(), target) {
            ("attach", "w1") => stream_worker(&mut writer),
            ("pause_workers", _) => write_json(
                &mut writer,
                &json!({ "type": "roster_update", "changed": roster("paused"), "removed": [] }),
            ),
            _ => {}
        }
    }
    asked
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
        session: SessionSelection::Attach("s1".to_string()),
        initial_message: None,
        show_images: true,
        screen_mode: eukhe_tui::screen_mode::ScreenMode::Fullscreen,
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
        dictation: None,
        daemon_launcher: None,
    }
}

fn key(code: KeyCode, modifiers: KeyModifiers) -> HeadlessStep {
    HeadlessStep::Key(KeyEvent::new(code, modifiers))
}

fn wait(needle: &str) -> HeadlessStep {
    HeadlessStep::WaitRender {
        needle: needle.to_string(),
        timeout_ms: 10_000,
    }
}

#[test]
fn the_worker_pane_shows_the_stream_and_esc_esc_pauses_the_worker() {
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
            wait("hello main"),
            // The pane splits to the right of main's chat (160 columns).
            wait("| worker - running"),
            wait("Context from you"),
            wait("use the v2 api"),
            wait("[note from main] asked mid-run"),
            wait("Folding in the context"),
            wait("read - src/api.rs"),
            // The full view, and Esc back to the split.
            key(KeyCode::Char('W'), KeyModifiers::SHIFT | KeyModifiers::ALT),
            wait("Esc: back"),
            key(KeyCode::Esc, KeyModifiers::NONE),
            HeadlessStep::WaitGone {
                needle: "Esc: back".to_string(),
                timeout_ms: 10_000,
            },
            // Esc Esc while the worker runs: pause.
            key(KeyCode::Esc, KeyModifiers::NONE),
            key(KeyCode::Esc, KeyModifiers::NONE),
            wait("| worker - paused"),
            wait("1 paused"),
            // Alt+W hides the pane.
            key(KeyCode::Char('w'), KeyModifiers::ALT),
            HeadlessStep::WaitGone {
                needle: "| worker - paused".to_string(),
                timeout_ms: 10_000,
            },
        ],
        width: 160,
        height: 40,
    };
    let frames = runtime
        .block_on(run_interactive(options(socket), UiMode::Headless(plan)))
        .expect("interactive run")
        .frames;
    let asked = handle.join().expect("mock supervisor finished");
    assert!(
        frames
            .iter()
            .all(|frame| !frame.contains("timed out waiting")),
        "every render condition held:\n{}",
        frames.join("\n---frame---\n")
    );
    assert_eq!(
        asked,
        vec![
            "attach:w1:watch".to_string(),
            "pause_workers:s1".to_string()
        ]
    );
    let shown = frames
        .iter()
        .find(|frame| frame.contains("Folding in the context"))
        .expect("a frame with the worker's text");
    assert_eq!(
        shown.matches("replayed prompt").count(),
        1,
        "the replayed frame the snapshot holds shows once:\n{shown}"
    );
}
