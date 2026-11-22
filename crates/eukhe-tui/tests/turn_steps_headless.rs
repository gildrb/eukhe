//! Headless e2e for the turn's step layout (the role gutter): the user
//! header's `>` mark, thinking collapsed to one row at `overview` and
//! expanded behind its bar at `details`, agent text at the text column,
//! one blank row between steps and before the reply, none inside a step.
//! A run that stops at its tool round cap says so instead of the no-reply
//! report.
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

const ANSWER: &str = "Fixed the greeting in `src/hello.rs`.\n\n\
    - `greet()` now prints `Hello, world!`\n- the test passes\n\n\
    ```rust\nfn greet() { println!(\"Hello, world!\"); }\n```";

const THINKING: &str =
    "The user wants the greeting fixed. First read `src/hello.rs` to see what it prints.\n\n\
    Then patch the string and run the tests. The read might fail if the path is wrong; \
    in that case list the directory.";

const CAP: &str = "The run stopped at its tool round cap: 250 rounds (maxToolRounds)";

/// How the scripted run ends.
#[derive(Clone, Copy)]
enum Ending {
    /// A second message answers.
    Answer,
    /// The run stops at its tool round cap after the first message's tools.
    Capped,
}

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
                "sessionName": "steps session",
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

fn assistant(content: &Value, stop: &str) -> Value {
    json!({
        "role": "assistant", "content": content, "api": "scripted",
        "provider": "scripted", "model": "faux-1",
        "usage": {
            "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 0,
            "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
        },
        "stopReason": stop, "timestamp": 1,
    })
}

fn tool_result(id: &str, name: &str, text: &str, is_error: bool) -> Value {
    json!({ "type": "tool_execution_end", "toolCallId": id, "toolName": name,
        "result": { "content": [{ "type": "text", "text": text }] }, "isError": is_error })
}

// One flat scripted event sequence: splitting it would scatter the
// turn's order across helpers.
#[allow(clippy::too_many_lines)]
fn stream_turn(writer: &mut UnixStream, ending: Ending) {
    let event = |payload: Value| json!({ "type": "session_event", "activeSessionId": "s1", "event": payload });
    let edit = "[src/hello.rs#AB12]\nPUT 2.=2:\n+    println!(\"Hello, world!\");";
    let first = assistant(
        &json!([
            { "type": "thinking", "thinking": THINKING },
            { "type": "text", "text": "Reading the file, then patching it." },
            { "type": "toolCall", "id": "tc-read", "name": "read", "arguments": { "path": "src/hello.rs" } },
            { "type": "toolCall", "id": "tc-edit", "name": "edit", "arguments": { "input": edit } },
            { "type": "toolCall", "id": "tc-test", "name": "bash", "arguments": { "script": "cargo test -q" } },
        ]),
        "toolUse",
    );
    let mut events = vec![
        json!({ "type": "agent_start" }),
        json!({ "type": "turn_start" }),
        json!({ "type": "message_start", "message": { "role": "user", "content": "fix the greeting in hello.rs", "timestamp": 1 } }),
        json!({ "type": "message_start", "message": assistant(&json!([{ "type": "text", "text": "" }]), "toolUse"), "assistantMessageEvent": { "type": "start" } }),
        json!({ "type": "message_end", "message": first }),
        json!({ "type": "tool_execution_start", "toolCallId": "tc-read", "toolName": "read", "args": { "path": "src/hello.rs" } }),
        tool_result("tc-read", "read", "[src/hello.rs#AB12]\n1:fn greet() {\n2:    println!(\"Helo world\");\n3:}\n4:\n5:fn main() { greet(); }", false),
        json!({ "type": "tool_execution_start", "toolCallId": "tc-edit", "toolName": "edit", "args": { "input": edit } }),
        tool_result("tc-edit", "edit", "[src/hello.rs#CD34]\n1:fn greet() {\n2:    println!(\"Hello, world!\");\n3:}", false),
        json!({ "type": "tool_execution_start", "toolCallId": "tc-test", "toolName": "bash", "args": { "script": "cargo test -q" } }),
        tool_result("tc-test", "bash", "error[E0425]: cannot find function `greet2` in this scope\n --> src/main.rs:9:5\nerror: could not compile `demo` (bin \"demo\") due to 1 previous error", true),
    ];
    match ending {
        Ending::Answer => {
            events.push(json!({ "type": "turn_end", "message": first, "toolResults": [] }));
            events.push(json!({ "type": "turn_start" }));
            let reply = assistant(
                &json!([
                    { "type": "thinking", "thinking": "The compile error is in a different file, unrelated to my patch. Report it." },
                    { "type": "text", "text": ANSWER },
                ]),
                "stop",
            );
            events.push(json!({ "type": "message_start", "message": assistant(&json!([{ "type": "text", "text": "" }]), "stop"), "assistantMessageEvent": { "type": "start" } }));
            events.push(json!({ "type": "message_end", "message": reply }));
            events.push(json!({ "type": "turn_end", "message": reply, "toolResults": [] }));
        }
        Ending::Capped => {
            events.push(
                json!({ "type": "turn_end", "message": first, "toolResults": [], "error": CAP }),
            );
        }
    }
    events.push(json!({ "type": "agent_end", "messages": [] }));
    for payload in events {
        write_json(writer, &event(payload));
    }
}

fn serve(listener: &UnixListener, ending: Ending) {
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
        let id = envelope
            .get("id")
            .and_then(Value::as_str)
            .unwrap_or("")
            .to_string();
        let command = envelope.get("command").cloned().unwrap_or(Value::Null);
        let kind = command
            .get("type")
            .and_then(Value::as_str)
            .unwrap_or_default()
            .to_string();
        match kind.as_str() {
            "create" => write_json(
                &mut writer,
                &response(
                    &id,
                    "create",
                    &json!({ "activeSessionId": "s1", "id": "s1", "sessionId": "sess-1", "sessionFile": "/tmp/sess-1.jsonl" }),
                ),
            ),
            "attach" => write_json(&mut writer, &response(&id, "attach", &attach_data())),
            "prompt" => {
                write_json(&mut writer, &response(&id, "prompt", &json!({})));
                stream_turn(&mut writer, ending);
            }
            _ => write_json(&mut writer, &response(&id, &kind, &json!({}))),
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

/// The fullscreen frames of the scripted turn at `overview`, then one
/// Ctrl+O (`details`).
fn run_turn(ending: Ending, needle: &str) -> Vec<String> {
    std::env::remove_var("TMUX");
    let dir = tempfile::TempDir::new().expect("temp dir");
    let socket = dir.path().join("tui.sock");
    let listener = UnixListener::bind(&socket).expect("bind mock socket");
    let handle = std::thread::spawn(move || serve(&listener, ending));
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .expect("tokio runtime");
    let steps = vec![
        HeadlessStep::WaitMs(200),
        HeadlessStep::Submit("fix the greeting in hello.rs".to_string()),
        HeadlessStep::WaitIdle { timeout_ms: 10_000 },
        HeadlessStep::WaitRender {
            needle: needle.to_string(),
            timeout_ms: 10_000,
        },
        HeadlessStep::WaitMs(300),
        ctrl_o(),
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
    outcome.frames
}

/// The frame's transcript from the user header to the last non-blank row
/// before the dock, trailing spaces cut and each tool row's elapsed time
/// (`- 3ms`) read as `- Nms`.
fn transcript(frame: &str) -> String {
    let rows: Vec<String> = frame
        .lines()
        .map(|row| elapsed_free(row.trim_end()))
        .collect();
    let start = rows
        .iter()
        .position(|row| row.starts_with(" > fix the greeting"))
        .unwrap_or_else(|| panic!("the user header renders:\n{frame}"));
    let end = rows
        .iter()
        .rposition(|row| row.starts_with('>'))
        .unwrap_or(rows.len());
    let body = &rows[start..end];
    let last = body.iter().rposition(|row| !row.is_empty()).unwrap_or(0);
    body[..=last].join("\n")
}

fn elapsed_free(row: &str) -> String {
    let mut out = String::new();
    let mut rest = row;
    while let Some(at) = rest.find("ms") {
        let head = &rest[..at];
        let digits = head.len() - head.trim_end_matches(|c: char| c.is_ascii_digit()).len();
        if digits > 0 && head[..head.len() - digits].ends_with(' ') {
            out.push_str(&head[..head.len() - digits]);
            out.push_str("Nms");
        } else {
            out.push_str(head);
            out.push_str("ms");
        }
        rest = &rest[at + 2..];
    }
    out.push_str(rest);
    out
}

fn assert_ascii(frames: &[String]) {
    for (index, frame) in frames.iter().enumerate() {
        for row in frame.lines() {
            assert!(row.is_ascii(), "frame {index} is ASCII: {row:?}");
        }
    }
}

const OVERVIEW: &str = " > fix the greeting in hello.rs

   + thinking: The user wants the greeting fixed. First read src/hello.rs to see what it prints.
     Reading the file, then patching it.
   ok read  src/hello.rs - 6 lines - Nms
   ok edit  src/hello.rs - +1 -1 - Nms
   x  bash  cargo test -q - 3 lines - Nms
      | error[E0425]: cannot find function `greet2` in this scope
      |  --> src/main.rs:9:5
      | error: could not compile `demo` (bin \"demo\") due to 1 previous error

   + thinking: The compile error is in a different file, unrelated to my patch. Report it.

     Fixed the greeting in src/hello.rs.

     - greet() now prints Hello, world!
     - the test passes

       fn greet() { println!(\"Hello, world!\"); }";

/// The rows `details` shows: each thinking expanded behind its bar.
const DETAILS: [&str; 4] = [
    "   - thinking",
    "   | The user wants the greeting fixed. First read src/hello.rs to see what it prints.",
    "   | The compile error is in a different file, unrelated to my patch. Report it.",
    "     Reading the file, then patching it.",
];

#[test]
fn a_turn_reads_as_steps_in_the_role_gutter() {
    let frames = run_turn(Ending::Answer, "Fixed the greeting");
    assert_ascii(&frames);
    let overview = frames
        .iter()
        .rev()
        .find(|frame| frame.contains("+ thinking:") && frame.contains("Fixed the greeting"))
        .expect("an overview frame with the answer");
    let details = frames.last().expect("frames");
    assert_eq!(transcript(overview), OVERVIEW);
    let details = transcript(details);
    for row in DETAILS {
        assert!(
            details.lines().any(|line| line == row),
            "{row:?} in:\n{details}"
        );
    }
    assert!(!details.contains("+ thinking"), "{details}");
}

#[test]
fn a_run_stopped_at_its_tool_round_cap_says_so() {
    let frames = run_turn(Ending::Capped, "maxToolRounds");
    assert_ascii(&frames);
    let last = frames.last().expect("frames");
    assert!(last.contains(CAP), "the cap row renders:\n{last}");
    assert!(
        !last.contains("No other configured model") && !last.contains("ended without a reply"),
        "no no-reply report for a capped run:\n{last}"
    );
}
