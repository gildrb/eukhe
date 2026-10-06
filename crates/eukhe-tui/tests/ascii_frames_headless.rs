//! Headless e2e for the ASCII-only CLI: a chat turn with thinking,
//! markdown, a successful tool run, and a failing tool run renders every
//! captured frame (history rows plus the live area, at every detail
//! level) as ASCII when the daemon's content is ASCII. Everything eukhe
//! draws itself (chrome, cards, borders, spinners, hints, the dock) comes
//! from the ASCII glyph table.
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
use serde_json::{json, Value};

/// The assistant's final markdown: every block kind the transcript
/// renderer draws chrome for.
const ANSWER: &str = "## Result\n\n\
    The listing worked; the read failed.\n\n\
    - first item\n- second item\n  1. nested\n\n\
    > a quoted line\n\n\
    ```rust\nfn main() {}\n```\n\n\
    | Task | State |\n| --- | --- |\n| list | done |\n| read | failed |\n\n\
    ---\n\n\
    See the [docs](https://example.com/docs).";

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
                "prompt" => {
                    write_json(&mut writer, &response(id, "prompt", &json!({})));
                    stream_turn(&mut writer);
                }
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

/// An idle, empty session (the new-chat splash renders).
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
            "messages": [],
            "lastEventSequence": 0,
            "lastEventCursor": null,
        },
        "client": { "id": "mock", "capabilities": [] },
        "lastEventSequence": 0,
        "lastEventCursor": null,
    })
}

fn tool_calls() -> Value {
    json!([
        { "type": "toolCall", "id": "tc-ls", "name": "bash", "arguments": { "command": "ls -la" } },
        { "type": "toolCall", "id": "tc-read", "name": "read", "arguments": { "path": "/tmp/missing.txt" } },
    ])
}

/// One scripted turn: thinking, streamed text with two tool calls, a
/// streamed successful bash run, a failing read, and the final answer.
// One flat scripted event sequence: splitting it would scatter the
// turn's order across helpers.
#[allow(clippy::too_many_lines)]
fn stream_turn(writer: &mut UnixStream) {
    let event = |payload: Value| json!({ "type": "session_event", "activeSessionId": "s1", "event": payload });
    let mut first = vec![
        json!({ "type": "thinking", "thinking": "Plan: list the directory, then read the file." }),
        json!({ "type": "text", "text": "Checking the directory." }),
    ];
    first.extend(tool_calls().as_array().expect("tool calls").iter().cloned());
    let first = Value::Array(first);
    write_json(writer, &event(json!({ "type": "agent_start" })));
    write_json(writer, &event(json!({ "type": "turn_start" })));
    write_json(
        writer,
        &event(json!({
            "type": "message_start",
            "message": { "role": "user", "content": "list and read" },
        })),
    );
    write_json(
        writer,
        &event(json!({
            "type": "message_start",
            "message": { "role": "assistant", "content": [{ "type": "text", "text": "" }] },
            "assistantMessageEvent": { "type": "start" },
        })),
    );
    write_json(
        writer,
        &event(json!({
            "type": "message_update",
            "message": { "role": "assistant", "content": first },
            "assistantMessageEvent": { "type": "text_delta", "delta": "Checking the directory." },
        })),
    );
    write_json(
        writer,
        &event(json!({
            "type": "message_end",
            "message": { "role": "assistant", "content": first },
        })),
    );
    write_json(
        writer,
        &event(json!({
            "type": "tool_execution_start",
            "toolCallId": "tc-ls",
            "toolName": "bash",
            "args": { "command": "ls -la" },
        })),
    );
    write_json(
        writer,
        &event(json!({
            "type": "tool_execution_update",
            "toolCallId": "tc-ls",
            "partialResult": { "content": [{ "type": "text", "text": "total 8\n" }] },
        })),
    );
    write_json(
        writer,
        &event(json!({
            "type": "tool_execution_end",
            "toolCallId": "tc-ls",
            "result": {
                "content": [{
                    "type": "text",
                    "text": "total 8\ndrwxr-xr-x 2 user user 4096 Jan 1 00:00 .\n-rw-r--r-- 1 user user  12 Jan 1 00:00 notes.txt\nlisting output done",
                }],
            },
            "isError": false,
        })),
    );
    write_json(
        writer,
        &event(json!({
            "type": "tool_execution_start",
            "toolCallId": "tc-read",
            "toolName": "read",
            "args": { "path": "/tmp/missing.txt" },
        })),
    );
    write_json(
        writer,
        &event(json!({
            "type": "tool_execution_end",
            "toolCallId": "tc-read",
            "result": {
                "content": [{ "type": "text", "text": "ENOENT: no such file or directory, open '/tmp/missing.txt'" }],
            },
            "isError": true,
        })),
    );
    let answer = json!([{ "type": "text", "text": ANSWER }]);
    write_json(
        writer,
        &event(json!({
            "type": "message_start",
            "message": { "role": "assistant", "content": [{ "type": "text", "text": "" }] },
            "assistantMessageEvent": { "type": "start" },
        })),
    );
    write_json(
        writer,
        &event(json!({
            "type": "message_end",
            "message": { "role": "assistant", "content": answer },
        })),
    );
    write_json(writer, &event(json!({ "type": "turn_end" })));
    write_json(writer, &event(json!({ "type": "agent_end" })));
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

fn ctrl_o() -> HeadlessStep {
    HeadlessStep::Key(KeyEvent::new(KeyCode::Char('o'), KeyModifiers::CONTROL))
}

#[test]
fn a_tool_turn_renders_only_ascii_frames() {
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
            HeadlessStep::WaitMs(200),
            // The slash menu's popup draws its own chrome.
            HeadlessStep::Type("/".to_string()),
            HeadlessStep::SettleIdle,
            HeadlessStep::Key(KeyEvent::new(KeyCode::Esc, KeyModifiers::NONE)),
            HeadlessStep::Submit("list and read".to_string()),
            HeadlessStep::WaitIdle { timeout_ms: 10_000 },
            HeadlessStep::WaitRender {
                needle: "See the docs".to_string(),
                timeout_ms: 10_000,
            },
            // Walk every detail level: the expanded cards draw the tool
            // output and the thinking block.
            ctrl_o(),
            HeadlessStep::WaitMs(100),
            ctrl_o(),
            HeadlessStep::WaitMs(100),
            ctrl_o(),
            HeadlessStep::WaitMs(100),
        ],
        width: 100,
        height: 40,
    };
    let outcome = runtime
        .block_on(run_interactive(options(socket), UiMode::Headless(plan)))
        .expect("interactive run");
    drop(runtime);
    handle.join().expect("mock supervisor finished");

    let all = outcome.frames.join("\n---frame---\n");
    for needle in [
        "list and read",
        "listing output done",
        "ENOENT",
        "See the docs",
    ] {
        assert!(all.contains(needle), "the turn rendered {needle:?}:\n{all}");
    }
    let offenders: Vec<String> = outcome
        .frames
        .iter()
        .enumerate()
        .flat_map(|(index, frame)| {
            frame
                .lines()
                .filter(|line| !line.is_ascii())
                .map(move |line| format!("frame {index}: {line:?}"))
        })
        .collect();
    assert!(
        offenders.is_empty(),
        "every frame byte is ASCII; non-ASCII rows:\n{}",
        offenders.join("\n")
    );
}
