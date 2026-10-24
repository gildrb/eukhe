//! Headless e2e for the fullscreen chat's text selection: left-button
//! reports drive the compiled selection model, and its release copies
//! the selected transcript text through the OSC 52 sink.
#![cfg(unix)]

use std::io::{BufRead, BufReader, Write};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::PathBuf;
use std::time::{Duration, Instant};

use base64::Engine as _;
use crossterm::event::{KeyCode, KeyEvent, KeyModifiers, MouseButton, MouseEvent, MouseEventKind};
use eukhe_tui::interactive::{
    run_interactive, HeadlessPlan, HeadlessStep, InteractiveOptions, ModelSelection,
    SessionSelection, UiMode,
};
use eukhe_tui::screen_mode::ScreenMode;
use serde_json::{json, Value};

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
        let idle_until = Instant::now() + Duration::from_secs(10);
        let (stream, _) = loop {
            match self.listener.accept() {
                Ok(accepted) => break accepted,
                Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                    if Instant::now() >= idle_until {
                        return;
                    }
                    std::thread::sleep(Duration::from_millis(10));
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
                    &response(
                        id,
                        "create",
                        &json!({
                            "activeSessionId": "s1",
                            "id": "s1",
                            "sessionId": "sess-1",
                            "sessionFile": "/tmp/sess-1.jsonl",
                        }),
                    ),
                ),
                "attach" => write_json(&mut writer, &response(id, "attach", &attach_data())),
                _ => write_json(&mut writer, &response(id, &command_type, &json!({}))),
            }
        }
    }
}

fn response(id: &str, command: &str, data: &Value) -> Value {
    json!({
        "type": "response",
        "id": id,
        "command": command,
        "success": true,
        "data": data,
    })
}

fn write_json(writer: &mut UnixStream, value: &Value) {
    let mut line = serde_json::to_string(value).expect("serialize mock frame");
    line.push('\n');
    writer.write_all(line.as_bytes()).expect("write mock frame");
    writer.flush().expect("flush mock frame");
}

/// An idle session with one user message of two lines.
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
                "sessionName": "ascii session",
                "model": null,
                "isStreaming": false,
                "isCompacting": false,
                "sessionActions": { "queuedCount": 0, "steering": [], "followUps": [] },
            },
            "messages": [
                { "role": "user", "content": [{ "type": "text", "text": "alpha bravo\ncharlie delta" }], "timestamp": 1 },
            ],
            "lastEventSequence": 0,
            "lastEventCursor": null,
        },
        "client": { "id": "mock", "capabilities": [] },
        "lastEventSequence": 0,
        "lastEventCursor": null,
    })
}

fn options(socket: PathBuf, screen_mode: ScreenMode) -> InteractiveOptions {
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
        screen_mode,
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

fn run(steps: Vec<HeadlessStep>) -> eukhe_tui::interactive::InteractiveOutcome {
    std::env::remove_var("TMUX");
    // No platform clipboard tool: the copy is the OSC 52 request.
    std::env::remove_var("DISPLAY");
    std::env::remove_var("WAYLAND_DISPLAY");
    let dir = tempfile::TempDir::new().expect("temp dir");
    let socket = dir.path().join("tui.sock");
    let supervisor = MockSupervisor::bind(&socket);
    let handle = std::thread::spawn(move || supervisor.serve());
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .expect("tokio runtime");
    let plan = HeadlessPlan {
        steps,
        width: WIDTH,
        height: HEIGHT,
    };
    let outcome = runtime
        .block_on(run_interactive(
            options(socket, ScreenMode::Fullscreen),
            UiMode::Headless(plan),
        ))
        .expect("interactive run");
    drop(runtime);
    handle.join().expect("mock supervisor finished");
    outcome
}

const WIDTH: u16 = 80;
const HEIGHT: u16 = 20;

fn shown() -> HeadlessStep {
    HeadlessStep::WaitRender {
        needle: "charlie delta".to_string(),
        timeout_ms: 10_000,
    }
}

fn mouse(kind: MouseEventKind, column: u16, row: u16) -> HeadlessStep {
    HeadlessStep::Mouse(MouseEvent {
        kind,
        column,
        row,
        modifiers: KeyModifiers::NONE,
    })
}

/// The screen cell of `needle`'s first character in `frame`.
fn cell_of(frame: &str, needle: &str) -> (u16, u16) {
    frame
        .split('\n')
        .enumerate()
        .find_map(|(row, line)| {
            line.find(needle).map(|col| {
                (
                    u16::try_from(line[..col].chars().count()).expect("col"),
                    u16::try_from(row).expect("row"),
                )
            })
        })
        .unwrap_or_else(|| panic!("{needle:?} on screen:\n{frame}"))
}

/// The base64 payloads of the OSC 52 requests in `emissions`.
fn osc52_payloads(emissions: &[String]) -> Vec<String> {
    let all = emissions.concat();
    all.split("\x1b]52;c;")
        .skip(1)
        .map(|rest| {
            rest.split(['\x07', '\x1b'])
                .next()
                .unwrap_or_default()
                .to_string()
        })
        .collect()
}

/// A drag in the fullscreen chat from "bravo" on one row to the end of
/// "charlie" on the next copies exactly that text through OSC 52 (the
/// soft newline between the rows kept); Esc then clears the selection,
/// and a second release copies nothing more.
#[test]
fn a_drag_across_two_rows_copies_the_exact_text_and_esc_clears() {
    let frames = run(vec![shown()]).frames;
    let frame = frames.last().expect("a frame");
    let (start_col, start_row) = cell_of(frame, "bravo");
    let (end_col, end_row) = cell_of(frame, "charlie");
    assert_eq!(end_row, start_row + 1, "two adjacent rows:\n{frame}");

    let left = MouseButton::Left;
    let outcome = run(vec![
        shown(),
        mouse(MouseEventKind::Down(left), start_col, start_row),
        HeadlessStep::WaitMs(30),
        mouse(MouseEventKind::Drag(left), start_col + 2, start_row),
        HeadlessStep::WaitMs(30),
        mouse(MouseEventKind::Drag(left), end_col + 6, end_row),
        HeadlessStep::WaitMs(30),
        mouse(MouseEventKind::Up(left), end_col + 6, end_row),
        HeadlessStep::WaitRender {
            needle: "Copied selection".to_string(),
            timeout_ms: 10_000,
        },
        HeadlessStep::Key(KeyEvent::new(KeyCode::Esc, KeyModifiers::NONE)),
        HeadlessStep::WaitMs(50),
        // Shown, then cleared: this release has nothing to copy.
        mouse(MouseEventKind::Up(left), end_col, end_row),
        HeadlessStep::WaitMs(50),
    ]);
    let payloads = osc52_payloads(&outcome.clipboard_emissions);
    let texts: Vec<String> = payloads
        .iter()
        .map(|p| {
            String::from_utf8(
                base64::engine::general_purpose::STANDARD
                    .decode(p)
                    .expect("base64"),
            )
            .expect("utf8")
        })
        .collect();
    // The screen's text: "bravo" to its row's end, then the next row
    // from its first column through "charlie".
    let lines: Vec<&str> = frame.split('\n').collect();
    let first = lines[usize::from(start_row)][usize::from(start_col)..].trim_end();
    let second = &lines[usize::from(end_row)][..usize::from(end_col) + "charlie".len()];
    assert_eq!(first, "bravo");
    assert_eq!(
        texts,
        [format!("{first}\n{second}")],
        "{:?}",
        outcome.clipboard_emissions
    );
}
