//! Headless e2e for the chat memory's live updates in the inline client:
//! the compactor's `memory_update`s never make a transcript row. A turn
//! with three summaries around one tool run leaves the transcript holding
//! the tool row alone, while the status line's `mem` gauge moves from the
//! open-time size to the newest one with the nodes summarized since the
//! request began.
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

const PROMPT: &str = "probe the gauge";
const ANSWER: &str = "gauge probed";

/// The gauge the open-time `get_memory` seeds.
const SEEDED_GAUGE: &str = "mem 87/128K";

/// The gauge after the turn's three summaries: the newest view size and
/// the four nodes they built.
const LIVE_GAUGE: &str = "mem 91/128K ~4";

fn write_json(writer: &mut UnixStream, value: &Value) {
    let mut line = serde_json::to_string(value).expect("serialize mock frame");
    line.push('\n');
    writer.write_all(line.as_bytes()).expect("write mock frame");
    writer.flush().expect("flush mock frame");
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

fn event(event: &Value) -> Value {
    json!({
        "type": "session_event",
        "activeSessionId": "s1",
        "event": event,
    })
}

fn summarized(lines: &Value, view_bytes: u64) -> Value {
    event(&json!({
        "type": "memory_update",
        "update": { "kind": "summarized", "lines": lines, "viewBytes": view_bytes },
    }))
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
        "timestamp": 2,
    })
}

/// One scripted turn: a summary, a bash run, two more summaries, the
/// answer.
fn stream_turn(writer: &mut UnixStream) {
    write_json(writer, &event(&json!({ "type": "agent_start" })));
    write_json(writer, &event(&json!({ "type": "turn_start" })));
    write_json(
        writer,
        &event(&json!({
            "type": "message_start",
            "message": { "role": "user", "content": PROMPT, "timestamp": 1 },
        })),
    );
    write_json(
        writer,
        &summarized(
            &json!([{ "id": 41, "count": 1, "text": "user: probe the gauge" }]),
            90_100,
        ),
    );
    write_json(
        writer,
        &event(&json!({
            "type": "tool_execution_start",
            "toolCallId": "tc-echo",
            "toolName": "bash",
            "args": { "command": "echo hi" },
        })),
    );
    write_json(
        writer,
        &event(&json!({
            "type": "tool_execution_end",
            "toolCallId": "tc-echo",
            "toolName": "bash",
            "result": { "content": [{ "type": "text", "text": "hi\n" }] },
            "isError": false,
        })),
    );
    write_json(
        writer,
        &summarized(
            &json!([
                { "id": 42, "count": 1, "text": "tool: echo hi" },
                { "id": 43, "count": 1, "text": "tool: hi" },
            ]),
            90_600,
        ),
    );
    write_json(
        writer,
        &summarized(&json!([{ "id": 40, "count": 4, "text": "probed" }]), 91_000),
    );
    let answer = json!([{ "type": "text", "text": ANSWER }]);
    write_json(
        writer,
        &event(&json!({
            "type": "message_start",
            "message": assistant(&json!([{ "type": "text", "text": "" }])),
            "assistantMessageEvent": { "type": "start" },
        })),
    );
    write_json(
        writer,
        &event(&json!({
            "type": "message_end",
            "message": assistant(&answer),
        })),
    );
    write_json(writer, &event(&json!({ "type": "turn_end" })));
    write_json(
        writer,
        &event(&json!({ "type": "agent_end", "messages": [] })),
    );
}

/// The mock supervisor: the hello, `attach`, `get_memory` (the seeding
/// status), the turn on `prompt`, and an empty success for everything
/// else.
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
        let command_type = envelope["command"]["type"]
            .as_str()
            .unwrap_or_default()
            .to_string();
        let data = match command_type.as_str() {
            "attach" => attach_data(),
            "get_memory" => json!({
                "memory": {
                    "status": {
                        "messages": 2,
                        "lines": 2,
                        "viewBytes": 87_200,
                        "unsummarized": 0,
                        "running": 0,
                        "model": null,
                        "lastError": null,
                    },
                    "text": "0+1|user: hello\n1+1|talk: settled answer",
                },
            }),
            _ => json!({}),
        };
        write_json(&mut writer, &response(id, &command_type, &data));
        if command_type == "prompt" {
            stream_turn(&mut writer);
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
                "sessionName": "gauge probe",
                "model": "faux-1",
                "isStreaming": false,
                "isCompacting": false,
                "sessionActions": { "queuedCount": 0, "steering": [], "followUps": [] },
            },
            "messages": [
                { "role": "user", "content": "hello", "timestamp": 1 },
                assistant(&json!([{ "type": "text", "text": "settled answer" }])),
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
        dictation: None,
        daemon_launcher: None,
    }
}

/// The transcript rows of `frame` between the turn's prompt and its
/// answer, trailing padding trimmed, blanks dropped.
fn turn_rows(frame: &str) -> Vec<String> {
    let lines: Vec<&str> = frame.lines().map(str::trim_end).collect();
    let prompt = lines
        .iter()
        .position(|line| line.contains(PROMPT))
        .expect("the prompt row");
    let answer = lines
        .iter()
        .position(|line| line.contains(ANSWER))
        .expect("the answer row");
    lines[prompt + 1..answer]
        .iter()
        .filter(|line| !line.trim().is_empty())
        .map(|line| (*line).to_string())
        .collect()
}

#[test]
fn memory_updates_move_the_gauge_and_never_the_transcript() {
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
            wait(SEEDED_GAUGE),
            HeadlessStep::Submit(PROMPT.to_string()),
            wait(ANSWER),
            wait(LIVE_GAUGE),
            HeadlessStep::WaitIdle { timeout_ms: 10_000 },
        ],
        width: 120,
        height: 30,
    };
    let frames = runtime
        .block_on(run_interactive(options(socket), UiMode::Headless(plan)))
        .expect("interactive run")
        .frames;
    handle.join().expect("mock supervisor finished");
    let all = || frames.join("\n---frame---\n");
    let last = frames
        .last()
        .unwrap_or_else(|| panic!("frames:\n{}", all()));
    let status = last
        .lines()
        .rev()
        .find(|line| line.contains("mem "))
        .unwrap_or_else(|| panic!("the status line's gauge:\n{}", all()));
    assert!(
        status.contains(LIVE_GAUGE),
        "the gauge reads the newest view size and the nodes summarized: {status:?}"
    );
    let rows = turn_rows(last);
    assert_eq!(
        rows.len(),
        1,
        "the turn's transcript holds the tool row alone:\n{rows:#?}\n{last}"
    );
    assert!(
        rows[0].contains("bash") && rows[0].contains("echo hi"),
        "the one row is the tool's: {:?}",
        rows[0]
    );
    for needle in ["memory:", "summarized", "41+1", "42+1", "43+1", "40+4"] {
        assert!(
            frames.iter().all(|frame| !frame.contains(needle)),
            "a memory update never reaches the transcript ({needle:?}):\n{}",
            all()
        );
    }
}
