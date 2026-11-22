//! Headless e2e for the engine continuations: a Director reminder the
//! daemon carries as a hidden custom message shows as one dim
//! `[reminder]` row between the user's prompt and the turn's first step,
//! while the turn streams and after a re-attach rebuilds the transcript
//! from the snapshot. Every frame byte is ASCII.
#![cfg(unix)]

use std::io::{BufRead, BufReader, Write};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::PathBuf;
use std::time::{Duration, Instant};

use crossterm::event::{KeyCode, KeyEvent, KeyModifiers};
use eukhe_tui::interactive::{
    run_interactive, HeadlessPlan, HeadlessStep, InteractiveOptions, ModelSelection,
    SessionSelection, UiMode,
};
use eukhe_tui::screen_mode::ScreenMode;
use serde_json::{json, Value};

const PROMPT: &str = "fix the greeting in hello.rs";
const REMINDER_ROW: &str = "   [reminder] Run the tests before you answer.";
const ANSWER: &str = "Fixed the greeting in src/hello.rs.";

/// The transcript the daemon holds after the turn: the prompt, the
/// Director's hidden reminder, a read, and the answer.
fn transcript() -> Vec<Value> {
    vec![
        json!({ "role": "user", "content": PROMPT, "timestamp": 1 }),
        reminder(),
        assistant(&json!([
            { "type": "thinking", "thinking": "Read the file first." },
            { "type": "text", "text": "Reading the file." },
            { "type": "toolCall", "id": "tc-read", "name": "read", "arguments": { "path": "src/hello.rs" } },
        ])),
        json!({
            "role": "toolResult",
            "toolCallId": "tc-read",
            "toolName": "read",
            "content": [{ "type": "text", "text": "fn greet() {}" }],
            "isError": false,
            "timestamp": 3,
        }),
        assistant(&json!([{ "type": "text", "text": ANSWER }])),
    ]
}

/// The Director's continuation as the daemon's wire carries it.
fn reminder() -> Value {
    json!({
        "role": "custom",
        "customType": "director_continuation",
        "content": "<system-reminder>Run the tests before you answer.</system-reminder>",
        "display": false,
        "details": { "origin": { "kind": "director" } },
        "timestamp": 2,
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
        "stopReason": "stop",
        "timestamp": 4,
    })
}

/// Serve one client: `attach` answers with `messages` as the snapshot's
/// transcript, `prompt` streams the turn live.
fn serve(listener: &UnixListener, messages: &[Value]) {
    listener
        .set_nonblocking(true)
        .expect("nonblocking listener");
    let idle_until = Instant::now() + Duration::from_secs(10);
    let stream = loop {
        match listener.accept() {
            Ok((stream, _)) => break stream,
            Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                if Instant::now() >= idle_until {
                    return;
                }
                std::thread::sleep(Duration::from_millis(10));
            }
            Err(_) => return,
        }
    };
    stream.set_nonblocking(false).expect("blocking connection");
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
        let command = envelope
            .get("command")
            .and_then(|command| command.get("type"))
            .and_then(Value::as_str)
            .unwrap_or_default()
            .to_string();
        match command.as_str() {
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
            "attach" => write_json(&mut writer, &response(id, "attach", &attach_data(messages))),
            "prompt" => {
                write_json(&mut writer, &response(id, "prompt", &json!({})));
                stream_turn(&mut writer);
            }
            _ => write_json(&mut writer, &response(id, &command, &json!({}))),
        }
    }
}

fn response(id: &str, command: &str, data: &Value) -> Value {
    json!({ "type": "response", "id": id, "command": command, "success": true, "data": data })
}

fn write_json(writer: &mut UnixStream, value: &Value) {
    let mut line = serde_json::to_string(value).expect("serialize mock frame");
    line.push('\n');
    writer.write_all(line.as_bytes()).expect("write mock frame");
    writer.flush().expect("flush mock frame");
}

fn attach_data(messages: &[Value]) -> Value {
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
                "sessionName": "injected session",
                "model": null,
                "isStreaming": false,
                "isCompacting": false,
                "sessionActions": { "queuedCount": 0, "steering": [], "followUps": [] },
            },
            "messages": messages,
            "lastEventSequence": 0,
            "lastEventCursor": null,
        },
        "client": { "id": "mock", "capabilities": [] },
        "lastEventSequence": 0,
        "lastEventCursor": null,
    })
}

/// The turn as live events: every message of the transcript starts and
/// ends, the read runs between them.
fn stream_turn(writer: &mut UnixStream) {
    let event = |payload: Value| json!({ "type": "session_event", "activeSessionId": "s1", "event": payload });
    write_json(writer, &event(json!({ "type": "agent_start" })));
    write_json(writer, &event(json!({ "type": "turn_start" })));
    for message in transcript() {
        if message["role"] == "toolResult" {
            write_json(
                writer,
                &event(json!({
                    "type": "tool_execution_start",
                    "toolCallId": "tc-read",
                    "toolName": "read",
                    "args": { "path": "src/hello.rs" },
                })),
            );
            write_json(
                writer,
                &event(json!({
                    "type": "tool_execution_end",
                    "toolCallId": "tc-read",
                    "toolName": "read",
                    "result": { "content": message["content"] },
                    "isError": false,
                })),
            );
            continue;
        }
        write_json(
            writer,
            &event(json!({ "type": "message_start", "message": message })),
        );
        write_json(
            writer,
            &event(json!({ "type": "message_end", "message": message })),
        );
    }
    write_json(writer, &event(json!({ "type": "turn_end" })));
    write_json(
        writer,
        &event(json!({ "type": "agent_end", "messages": [] })),
    );
}

fn options(socket: PathBuf) -> InteractiveOptions {
    InteractiveOptions {
        budget: None,
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
        screen_mode: ScreenMode::Fullscreen,
        theme: "forge".to_string(),
        code_block_indent: "  ".to_string(),
        tree_filter_mode: String::new(),
        branch_summary_skip_prompt: false,
        version: "0.0.0".to_string(),
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
        restart: None,
    }
}

fn ctrl_o() -> HeadlessStep {
    HeadlessStep::Key(KeyEvent::new(KeyCode::Char('o'), KeyModifiers::CONTROL))
}

/// Run `steps` against a mock daemon whose snapshot holds `messages`;
/// the captured frames.
fn run(messages: Vec<Value>, steps: Vec<HeadlessStep>) -> Vec<String> {
    std::env::remove_var("TMUX");
    let dir = tempfile::TempDir::new().expect("temp dir");
    let socket = dir.path().join("tui.sock");
    let listener = UnixListener::bind(&socket).expect("bind mock socket");
    let handle = std::thread::spawn(move || serve(&listener, &messages));
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .expect("tokio runtime");
    let plan = HeadlessPlan {
        steps,
        width: 100,
        height: 40,
    };
    let outcome = runtime
        .block_on(run_interactive(options(socket), UiMode::Headless(plan)))
        .expect("interactive run");
    drop(runtime);
    handle.join().expect("mock supervisor finished");
    outcome.frames
}

/// The steps after the turn shows: the answer settles, then each detail
/// level renders once.
fn detail_steps() -> Vec<HeadlessStep> {
    vec![
        HeadlessStep::WaitRender {
            needle: ANSWER.to_string(),
            timeout_ms: 10_000,
        },
        HeadlessStep::WaitMs(100),
        ctrl_o(),
        HeadlessStep::WaitMs(100),
        ctrl_o(),
        HeadlessStep::WaitMs(100),
    ]
}

/// The reminder row sits alone between the prompt and the first step,
/// one blank row on each side, in every frame that shows the answer.
fn assert_reminder_row(frames: &[String]) {
    let shown: Vec<&String> = frames
        .iter()
        .filter(|frame| frame.contains(ANSWER))
        .collect();
    assert!(shown.len() >= 3, "every detail level rendered: {frames:#?}");
    for frame in shown {
        let rows: Vec<&str> = frame.lines().map(str::trim_end).collect();
        let at = rows
            .iter()
            .position(|row| *row == REMINDER_ROW)
            .unwrap_or_else(|| panic!("the reminder row shows:\n{frame}"));
        assert!(
            rows[at - 2].contains(PROMPT) && rows[at - 1].is_empty() && rows[at + 1].is_empty(),
            "a blank row on each side, the prompt above:\n{frame}"
        );
        assert!(
            rows.get(at + 2).is_some_and(|row| !row.is_empty()),
            "the first step follows:\n{frame}"
        );
        assert_eq!(frame.matches("[reminder]").count(), 1, "{frame}");
        assert!(!frame.contains("system-reminder"), "{frame}");
    }
    for (index, frame) in frames.iter().enumerate() {
        assert!(frame.is_ascii(), "frame {index} is ASCII:\n{frame}");
    }
}

#[test]
fn a_director_reminder_shows_live() {
    let mut steps = vec![
        HeadlessStep::WaitMs(200),
        HeadlessStep::Submit(PROMPT.to_string()),
        HeadlessStep::WaitIdle { timeout_ms: 10_000 },
    ];
    steps.extend(detail_steps());
    assert_reminder_row(&run(Vec::new(), steps));
}

#[test]
fn a_director_reminder_shows_after_reattach() {
    assert_reminder_row(&run(transcript(), detail_steps()));
}
