//! Headless e2e for the chat memory in the inline client: the status
//! line's `mem` gauge seeds from the open-time `get_memory`, `/memory`
//! prints the status header and every view line as inline rows,
//! `/memory zoom <id> <n>` prints the zoom, a pushed `memory_update` lands
//! as a live row (no turn running) and moves the gauge, and malformed
//! arguments answer the usage.
#![cfg(unix)]
// - the futures are bounded by the surface's lifetime; boxing them would
//   add an allocation to the steady-state loop.
#![allow(clippy::large_futures)]

use std::io::{BufRead, BufReader, Write};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::PathBuf;

use eukhe_tui::interactive::{
    run_interactive, HeadlessPlan, HeadlessStep, InteractiveOptions, ModelSelection,
    SessionSelection, UiMode,
};
use serde_json::{json, Value};

/// The view the mock serves, frame already stripped.
const VIEW_TEXT: &str = "0+32|user: hi | bot: hello\n32+1|plan the release";

const HEADER: &str = "memory: 43 messages, view 87.2 KB / 128.0 KB (floor 64.0 KB), 2 lines, \
                      2 unsummarized, 1 compaction running, model anthropic/claude-haiku-4-5";

/// The two pushed summaries, coalesced into one live row.
const LIVE_ROW: &str = "memory: summarized 41+1, 42+1, 40+2 (view 91.0 KB)";

fn write_json(writer: &mut UnixStream, value: &Value) {
    let mut line = serde_json::to_string(value).expect("serialize mock frame");
    line.push('\n');
    writer.write_all(line.as_bytes()).expect("write mock frame");
    writer.flush().expect("flush mock frame");
}

fn status() -> Value {
    json!({
        "messages": 43,
        "lines": 2,
        "viewBytes": 87_200,
        "unsummarized": 2,
        "running": 1,
        "model": "anthropic/claude-haiku-4-5",
        "lastError": null,
    })
}

/// Serve one connection: the hello (with the `memory` lane), the attach
/// snapshot, `get_memory` (the view, or the zoom followed by one pushed
/// `memory_update`), and an empty success for everything else.
fn serve(listener: &UnixListener) {
    let (stream, _) = listener.accept().expect("accept");
    let mut writer = stream.try_clone().expect("clone mock socket");
    let mut reader = BufReader::new(stream);
    write_json(
        &mut writer,
        &json!({
            "type": "daemon_hello",
            "protocol": { "name": "eukhe.daemon", "version": 7 },
            "serverCapabilities": ["memory"],
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
        let command = &envelope["command"];
        let command_type = command["type"].as_str().unwrap_or_default().to_string();
        let zoomed = command_type == "get_memory" && !command["zoom"].is_null();
        let data = match command_type.as_str() {
            "attach" => attach_data(),
            "get_memory" if zoomed => {
                assert_eq!(command["zoom"], json!({ "id": 40, "count": 8 }));
                json!({
                    "memory": {
                        "status": status(),
                        "text": "40+4|first half\n44+4|second half",
                    },
                })
            }
            "get_memory" => {
                assert_eq!(command["activeSessionId"], "s1");
                json!({ "memory": { "status": status(), "text": VIEW_TEXT } })
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
        if zoomed {
            let pushes = [
                json!({
                    "kind": "summarized",
                    "lines": [
                        { "id": 41, "count": 1, "text": "user: ship it" },
                        { "id": 42, "count": 1, "text": "talk: shipped" },
                    ],
                    "viewBytes": 90_100,
                }),
                json!({
                    "kind": "summarized",
                    "lines": [{ "id": 40, "count": 2, "text": "shipped it" }],
                    "viewBytes": 91_000,
                }),
            ];
            for update in pushes {
                write_json(
                    &mut writer,
                    &json!({
                        "type": "session_event",
                        "activeSessionId": "s1",
                        "event": { "type": "memory_update", "update": update },
                    }),
                );
            }
        }
    }
}

fn attach_data() -> Value {
    json!({
        "protocol": { "name": "eukhe.daemon", "version": 7 },
        "activeSessionId": "s1",
        "snapshot": {
            "activeSessionId": "s1",
            "summary": { "id": "s1", "cwd": "/tmp" },
            "state": {
                "activeSessionId": "s1",
                "cwd": "/tmp",
                "sessionId": "sess-1",
                "sessionName": "memory probe",
                "model": "faux-1",
                "isStreaming": false,
                "isCompacting": false,
                "sessionActions": { "queuedCount": 0, "steering": [], "followUps": [] },
            },
            "messages": [
                { "role": "user", "content": "hello", "timestamp": 1 },
                { "role": "assistant", "content": "settled answer", "provider": "scripted", "model": "faux-1", "timestamp": 2 },
            ],
            "lastEventSequence": 0,
            "lastEventCursor": null,
        },
        "client": { "id": "mock", "capabilities": [] },
        "lastEventSequence": 0,
        "lastEventCursor": null,
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
        session: SessionSelection::Attach("s1".to_string()),
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

#[test]
fn memory_prints_the_view_zooms_and_shows_live_updates() {
    std::env::remove_var("TMUX");
    let dir = tempfile::TempDir::new().expect("temp dir");
    let socket = dir.path().join("tui.sock");
    let listener = UnixListener::bind(&socket).expect("bind mock socket");
    let handle = std::thread::spawn(move || serve(&listener));
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .expect("tokio runtime");
    let wait = |needle: &str| HeadlessStep::WaitRender {
        needle: needle.to_string(),
        timeout_ms: 10_000,
    };
    let plan = HeadlessPlan {
        steps: vec![
            // The open-time status seeds the gauge.
            wait("mem 87/128K"),
            HeadlessStep::Submit("/memory".to_string()),
            wait(HEADER),
            wait("32+1|plan the release"),
            HeadlessStep::Submit("/memory zoom 40 8".to_string()),
            wait("memory zoom 40+8:"),
            wait("44+4|second half"),
            // The update pushed after the zoom: a live row while no turn
            // runs, and the gauge follows it.
            wait(LIVE_ROW),
            wait("mem 91/128K"),
            HeadlessStep::Submit("/memory zoom 40".to_string()),
            wait("Usage: /memory [zoom <id> <n>]"),
        ],
        width: 200,
        height: 40,
    };
    let frames = runtime
        .block_on(run_interactive(options(socket), UiMode::Headless(plan)))
        .expect("interactive run")
        .frames;
    handle.join().expect("mock supervisor finished");
    assert!(
        frames.iter().all(|frame| !frame.contains("<chat>")),
        "the view prints without its frame:\n{}",
        frames.join("\n---frame---\n")
    );
    assert!(
        frames
            .iter()
            .all(|frame| !frame.contains("memory: summarized 40+2")),
        "the second update folds into the live row, never a row of its own:\n{}",
        frames.join("\n---frame---\n")
    );
}
