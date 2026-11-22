//! Headless e2e for the tool cards: a turn reads a file, edits it (the
//! result carries the numbered diff) and runs a failing build. At the
//! default detail the failed call shows its output behind the dim bar
//! under its row; at `details` the edit shows its diff with both line
//! marks; every transcript row is ASCII.
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

const PATCH: &str = "[src/hello.rs#AB12]\nPUT 2.=2:\n+    println!(\"Hello, world!\");";
const BUILD_ERROR: &str = "error[E0425]: cannot find function `greet2` in this scope\n --> src/main.rs:9:5\nerror: could not compile `demo` (bin \"demo\") due to 1 previous error";

fn write_json(writer: &mut UnixStream, value: &Value) {
    let mut line = serde_json::to_string(value).expect("serialize mock frame");
    line.push('\n');
    writer.write_all(line.as_bytes()).expect("write mock frame");
    writer.flush().expect("flush mock frame");
}

fn response(id: &str, command: &str, data: &Value) -> Value {
    json!({ "type": "response", "id": id, "command": command, "success": true, "data": data })
}

fn attach_data() -> Value {
    json!({
        "protocol": { "name": "eukhe.daemon", "version": 7 },
        "activeSessionId": "s1",
        "snapshot": {
            "activeSessionId": "s1",
            "summary": { "id": "s1", "cwd": "/tmp/demo" },
            "state": {
                "activeSessionId": "s1",
                "cwd": "/tmp/demo",
                "sessionId": "sess-1",
                "model": { "id": "claude-sonnet-4-5", "provider": "anthropic" },
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

fn assistant(content: &Value, stop: &str) -> Value {
    json!({
        "role": "assistant", "content": content, "api": "anthropic-messages",
        "provider": "anthropic", "model": "claude-sonnet-4-5",
        "usage": { "input": 10, "output": 10, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 20,
            "cost": { "input": 0.0, "output": 0.0, "cacheRead": 0.0, "cacheWrite": 0.0, "total": 0.0 } },
        "stopReason": stop, "timestamp": 1,
    })
}

/// The edit result's details as the edit tool sends them.
fn edit_details() -> Value {
    json!({
        "version": "edit@hl.1",
        "rendered": "[src/hello.rs#CD34]",
        "files": [{
            "path": "src/hello.rs",
            "absolute": "/tmp/demo/src/hello.rs",
            "change": "updated",
            "diff": " 1|fn greet() {\n-2|    println!(\"Helo world\");\n+2|    println!(\"Hello, world!\");\n 3|}",
            "first_changed_line": 2,
            "warnings": [],
            "tag": "CD34",
        }],
        "outcome": "done",
        "warnings": [],
    })
}

fn stream_turn(writer: &mut UnixStream) {
    let event = |payload: Value| json!({ "type": "session_event", "activeSessionId": "s1", "event": payload });
    let calls = json!([
        { "type": "text", "text": "Reading the file, then patching it." },
        { "type": "toolCall", "id": "tc-read", "name": "read", "arguments": { "path": "src/hello.rs" } },
        { "type": "toolCall", "id": "tc-edit", "name": "edit", "arguments": { "input": PATCH } },
        { "type": "toolCall", "id": "tc-test", "name": "bash", "arguments": { "script": "cargo test -q" } },
    ]);
    let answer = json!([{ "type": "text", "text": "Fixed the greeting in src/hello.rs." }]);
    for payload in [
        json!({ "type": "agent_start" }),
        json!({ "type": "turn_start" }),
        json!({ "type": "message_start", "message": { "role": "user", "content": "fix the greeting in hello.rs", "timestamp": 1 } }),
        json!({ "type": "message_start", "message": assistant(&json!([{ "type": "text", "text": "" }]), "toolUse"), "assistantMessageEvent": { "type": "start" } }),
        json!({ "type": "message_end", "message": assistant(&calls, "toolUse") }),
        json!({ "type": "tool_execution_start", "toolCallId": "tc-read", "toolName": "read", "args": { "path": "src/hello.rs" } }),
        json!({ "type": "tool_execution_end", "toolCallId": "tc-read", "toolName": "read",
            "result": { "content": [{ "type": "text", "text": "[src/hello.rs#AB12]\n1:fn greet() {\n2:    println!(\"Helo world\");\n3:}" }] }, "isError": false }),
        json!({ "type": "tool_execution_start", "toolCallId": "tc-edit", "toolName": "edit", "args": { "input": PATCH } }),
        json!({ "type": "tool_execution_end", "toolCallId": "tc-edit", "toolName": "edit",
            "result": { "content": [{ "type": "text", "text": "[src/hello.rs#CD34]\n1:fn greet() {\n2:    println!(\"Hello, world!\");\n3:}" }], "details": edit_details() }, "isError": false }),
        json!({ "type": "tool_execution_start", "toolCallId": "tc-test", "toolName": "bash", "args": { "script": "cargo test -q" } }),
        json!({ "type": "tool_execution_end", "toolCallId": "tc-test", "toolName": "bash",
            "result": { "content": [{ "type": "text", "text": BUILD_ERROR }] }, "isError": true }),
        json!({ "type": "message_start", "message": assistant(&json!([{ "type": "text", "text": "" }]), "stop"), "assistantMessageEvent": { "type": "start" } }),
        json!({ "type": "message_end", "message": assistant(&answer, "stop") }),
        json!({ "type": "turn_end" }),
        json!({ "type": "agent_end", "messages": [] }),
    ] {
        write_json(writer, &event(payload));
    }
}

fn serve(listener: &UnixListener) {
    listener
        .set_nonblocking(true)
        .expect("nonblocking mock listener");
    let idle_until = Instant::now() + Duration::from_secs(10);
    let (stream, _) = loop {
        match listener.accept() {
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
        &json!({ "type": "daemon_hello", "protocol": { "name": "eukhe.daemon", "version": 7 }, "serverCapabilities": [], "clientId": "mock" }),
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
                    &json!({ "activeSessionId": "s1", "id": "s1", "sessionId": "sess-1", "sessionFile": "/tmp/sess-1.jsonl" }),
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

fn options(socket: PathBuf) -> InteractiveOptions {
    InteractiveOptions {
        budget: None,
        models: None,
        socket_path: socket,
        cwd: PathBuf::from("/tmp/demo"),
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
        theme: "eukhe".to_string(),
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

/// The frames of the turn: the last one at `overview`, then the last one
/// at `details`.
fn run_turn() -> (String, String) {
    std::env::remove_var("TMUX");
    let dir = tempfile::TempDir::new().expect("temp dir");
    let socket = dir.path().join("tui.sock");
    let listener = UnixListener::bind(&socket).expect("bind mock socket");
    let handle = std::thread::spawn(move || serve(&listener));
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .expect("tokio runtime");
    let steps = vec![
        HeadlessStep::WaitMs(200),
        HeadlessStep::Submit("fix the greeting in hello.rs".to_string()),
        HeadlessStep::WaitIdle { timeout_ms: 10_000 },
        HeadlessStep::WaitRender {
            needle: "Fixed the greeting".to_string(),
            timeout_ms: 10_000,
        },
        HeadlessStep::WaitMs(300),
        HeadlessStep::Key(KeyEvent::new(KeyCode::Char('o'), KeyModifiers::CONTROL)),
        HeadlessStep::WaitMs(300),
    ];
    let plan = HeadlessPlan {
        steps,
        width: 100,
        height: 60,
    };
    let outcome = runtime
        .block_on(run_interactive(options(socket), UiMode::Headless(plan)))
        .expect("interactive run");
    drop(runtime);
    handle.join().expect("mock supervisor finished");
    let frames = outcome.frames;
    let offenders: Vec<&str> = frames
        .iter()
        .flat_map(|frame| frame.lines())
        .filter(|line| !line.starts_with(" [M] ") && !line.is_ascii())
        .collect();
    assert!(
        offenders.is_empty(),
        "non-ASCII transcript rows: {offenders:?}"
    );
    let overview = frames
        .iter()
        .rev()
        .find(|frame| frame.contains("Fixed the greeting") && !frame.contains(" - details"))
        .unwrap_or_else(|| panic!("an overview frame; the frames:\n{}", frames.join("\n---\n")))
        .clone();
    let details = frames.last().expect("frames").clone();
    (overview, details)
}

/// The rows from the first that starts with `first`, `count` of them,
/// right-trimmed, a tool row's run time (`- 3ms`) left out: the mock's
/// tools run on the real clock.
fn rows_from(frame: &str, first: &str, count: usize) -> Vec<String> {
    frame
        .lines()
        .skip_while(|line| !line.starts_with(first))
        .take(count)
        .map(|line| {
            let line = line.trim_end();
            match line.rsplit_once(" - ") {
                Some((head, last))
                    if last.strip_suffix("ms").is_some_and(|number| {
                        !number.is_empty() && number.bytes().all(|byte| byte.is_ascii_digit())
                    }) =>
                {
                    head.to_string()
                }
                _ => line.to_string(),
            }
        })
        .collect()
}

#[test]
fn failed_output_shows_by_default_and_the_edit_diff_at_details() {
    let (overview, details) = run_turn();
    assert_eq!(
        rows_from(&overview, "   x  bash", 4),
        [
            "   x  bash  cargo test -q - 3 lines",
            "      | error[E0425]: cannot find function `greet2` in this scope",
            "      |  --> src/main.rs:9:5",
            "      | error: could not compile `demo` (bin \"demo\") due to 1 previous error",
        ],
        "{overview}"
    );
    assert_eq!(
        rows_from(&overview, "   ok edit", 2),
        [
            "   ok edit  src/hello.rs - +1 -1",
            "   x  bash  cargo test -q - 3 lines",
        ],
        "{overview}"
    );
    assert_eq!(
        rows_from(&details, "   ok edit", 5),
        [
            "   ok edit  src/hello.rs - +1 -1",
            "       1   fn greet() {",
            "       2 -     println!(\"Helo world\");",
            "       2 +     println!(\"Hello, world!\");",
            "       3   }",
        ],
        "{details}"
    );
}
