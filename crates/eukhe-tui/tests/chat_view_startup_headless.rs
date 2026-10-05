//! Headless e2e for the startup chat-view block (`OptChat` spec §10: "On start,
//! print the view, so you see what the agent sees"): opening a session
//! shows the chat memory's view as one collapsed summary row that Ctrl+O
//! expands to the full `<chat>` text — and the first paint never waits
//! for it.
//!
//! The mock supervisor advertises the `chat_view` lane, serves the attach
//! snapshot at once, and answers `get_chat_view` only after a delay: the
//! transcript's content frame must paint before the view lands.
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

/// How late the mock answers `get_chat_view`: far past the content
/// frame's paint, so a first paint that waited on the view would show it.
const CHAT_VIEW_DELAY_MS: u64 = 500;

/// The view the mock serves: two parts over three messages.
const VIEW_TEXT: &str = "<chat>\n0+2|user: hi | bot: hello\n2+1|plan the release\n</chat>";

const SUMMARY: &str = "Chat view: 2 lines, 3 messages, 0.1 KB";

fn write_json(writer: &mut UnixStream, value: &Value) {
    let mut line = serde_json::to_string(value).expect("serialize mock frame");
    line.push('\n');
    writer.write_all(line.as_bytes()).expect("write mock frame");
    writer.flush().expect("flush mock frame");
}

/// Serve one connection: the hello (with the `chat_view` lane), the
/// attach snapshot of a settled exchange, the delayed `get_chat_view`,
/// and an empty success for everything else.
fn serve(listener: &UnixListener) {
    let (stream, _) = listener.accept().expect("accept");
    let mut writer = stream.try_clone().expect("clone mock socket");
    let mut reader = BufReader::new(stream);
    write_json(
        &mut writer,
        &json!({
            "type": "daemon_hello",
            "protocol": { "name": "eukhe.daemon", "version": 7 },
            "serverCapabilities": ["chat_view"],
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
        let command_type = envelope["command"]["type"]
            .as_str()
            .unwrap_or_default()
            .to_string();
        let data = match command_type.as_str() {
            "attach" => attach_data(),
            "get_chat_view" => {
                assert_eq!(envelope["command"]["activeSessionId"], "s1");
                std::thread::sleep(std::time::Duration::from_millis(CHAT_VIEW_DELAY_MS));
                json!({
                    "view": {
                        "text": VIEW_TEXT,
                        "messages": 3,
                        "lines": 2,
                        "bytes": VIEW_TEXT.len(),
                    },
                })
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
                "sessionName": "view probe",
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
        fullscreen_mouse: true,
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

fn ctrl_o() -> KeyEvent {
    KeyEvent::new(KeyCode::Char('o'), KeyModifiers::CONTROL)
}

/// The session opens into its transcript at once; the chat view lands
/// later as one collapsed summary row (never the `<chat>` text), and
/// Ctrl+O — cycled to the expanded level — shows the full view text.
#[test]
fn the_chat_view_lands_after_first_paint_and_expands() {
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
            wait(SUMMARY),
            // Overview -> Details -> All: tool output (and the view's
            // body with it) expands at All.
            HeadlessStep::Key(ctrl_o()),
            HeadlessStep::Key(ctrl_o()),
            wait("2+1|plan the release"),
        ],
        width: 100,
        height: 30,
    };
    let frames = runtime
        .block_on(run_interactive(options(socket), UiMode::Headless(plan)))
        .expect("interactive run")
        .frames;
    handle.join().expect("mock supervisor finished");
    let all = frames.join("\n---frame---\n");

    let content = frames
        .iter()
        .position(|frame| frame.contains("settled answer"))
        .unwrap_or_else(|| panic!("the transcript never painted:\n{all}"));
    let view = frames
        .iter()
        .position(|frame| frame.contains(SUMMARY))
        .unwrap_or_else(|| panic!("the chat view never landed:\n{all}"));
    assert!(
        content < view,
        "the content frame paints before the delayed view lands \
         (frame {content} vs {view}):\n{all}"
    );
    assert!(
        !frames[view].contains("<chat>"),
        "the block lands collapsed (summary only):\n{}",
        frames[view]
    );
    let last = frames.last().expect("frames were captured");
    for line in VIEW_TEXT.lines() {
        assert!(
            last.contains(line),
            "the expanded block shows the view line {line:?}:\n{last}"
        );
    }
}
