//! The turn's usage footer end to end: a mock daemon streams one turn (a
//! tool round with three calls, the test run exiting nonzero, then the
//! answer) with provider usage and stream timings; the live chat closes
//! the turn with its footer, which counts the call its card marks `x`
//! failed, the status line shows the running turn's `cache NN%`
//! meanwhile, and a re-attach to the stored transcript folds the same
//! footer.
#![cfg(unix)]

use std::io::{BufRead, BufReader, Write};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::PathBuf;
use std::time::{Duration, Instant};

use eukhe_tui::interactive::{
    run_interactive, HeadlessPlan, HeadlessStep, InteractiveOptions, ModelSelection,
    SessionSelection, UiMode,
};
use eukhe_tui::screen_mode::ScreenMode;
use serde_json::{json, Value};

const FOOTER: &str =
    "   -- 4.2s - 3 tools, 1 failed - in 1.9k - out 352 - cache r 80.1k w 2.0k (95% hit) - $0.06";

fn write_json(writer: &mut UnixStream, value: &Value) {
    let mut line = serde_json::to_string(value).expect("encodes");
    line.push('\n');
    writer.write_all(line.as_bytes()).expect("writes");
    writer.flush().expect("flushes");
}

fn response(id: &str, command: &str, data: &Value) -> Value {
    json!({ "type": "response", "id": id, "command": command, "success": true, "data": data })
}

fn usage(input: u64, output: u64, cache_read: u64, cache_write: u64) -> Value {
    json!({
        "input": input, "output": output, "cacheRead": cache_read, "cacheWrite": cache_write,
        "totalTokens": input + output + cache_read + cache_write,
        "cost": { "input": 0.0, "output": 0.0, "cacheRead": 0.0, "cacheWrite": 0.0, "total": 0.028 },
    })
}

fn assistant(
    content: &Value,
    usage: &Value,
    stop: &str,
    timestamp: u64,
    last_token_ms: u64,
) -> Value {
    json!({
        "role": "assistant", "content": content, "api": "anthropic-messages",
        "provider": "anthropic", "model": "claude-sonnet-4-5", "usage": usage,
        "stopReason": stop, "timestamp": timestamp,
        "timing": { "firstByteMs": 1, "firstTokenMs": 2, "lastTokenMs": last_token_ms },
    })
}

fn user() -> Value {
    json!({ "role": "user", "content": "fix the greeting in hello.rs", "timestamp": 900 })
}

/// The tool round: three calls, read and edit fine, the test run failing.
fn tool_round() -> Value {
    assistant(
        &json!([
            { "type": "text", "text": "Reading the file, then patching it." },
            { "type": "toolCall", "id": "tc-read", "name": "read", "arguments": { "path": "src/hello.rs" } },
            { "type": "toolCall", "id": "tc-edit", "name": "edit", "arguments": { "input": "x" } },
            { "type": "toolCall", "id": "tc-test", "name": "bash", "arguments": { "script": "cargo test -q" } },
        ]),
        &usage(1840, 212, 38912, 2048),
        "toolUse",
        1_000,
        1_500,
    )
}

fn answer() -> Value {
    assistant(
        &json!([{ "type": "text", "text": "Fixed the greeting in src/hello.rs." }]),
        &usage(96, 140, 41200, 0),
        "stop",
        3_000,
        2_200,
    )
}

/// The three tool results: `(id, name, text, is_error)`. The test run is
/// no error result: its script exits 101 ([`details`]).
const RESULTS: [(&str, &str, &str, bool); 3] = [
    ("tc-read", "read", "fn greet() {}", false),
    ("tc-edit", "edit", "patched", false),
    (
        "tc-test",
        "bash",
        "error[E0425]: cannot find function `greet2`",
        false,
    ),
];

/// A result's details: the bash script's nonzero exit.
fn details(name: &str) -> Value {
    if name == "bash" {
        json!({ "version": "bash@1", "steps": [], "end": { "kind": "finished", "status": 101 } })
    } else {
        Value::Null
    }
}

fn attach_data(messages: &Value) -> Value {
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
                "contextUsage": { "tokens": 43210, "contextWindow": 200_000 },
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

/// The stored transcript of the turn, as a re-attach reads it.
fn stored_turn() -> Value {
    let mut messages = vec![user(), tool_round()];
    messages.extend(RESULTS.iter().map(|(id, name, text, is_error)| {
        json!({
            "role": "toolResult", "toolCallId": id, "toolName": name,
            "content": [{ "type": "text", "text": text }], "details": details(name),
            "isError": is_error, "timestamp": 2_000,
        })
    }));
    messages.push(answer());
    Value::Array(messages)
}

fn stream_turn(writer: &mut UnixStream) {
    let send = |writer: &mut UnixStream, payload: Value| {
        write_json(
            writer,
            &json!({ "type": "session_event", "activeSessionId": "s1", "event": payload }),
        );
    };
    send(writer, json!({ "type": "agent_start" }));
    send(writer, json!({ "type": "turn_start" }));
    send(
        writer,
        json!({ "type": "message_start", "message": user() }),
    );
    send(
        writer,
        json!({ "type": "message_start", "message": tool_round(), "assistantMessageEvent": { "type": "start" } }),
    );
    send(
        writer,
        json!({ "type": "message_end", "message": tool_round() }),
    );
    for (id, name, text, is_error) in RESULTS {
        send(
            writer,
            json!({ "type": "tool_execution_start", "toolCallId": id, "toolName": name, "args": {} }),
        );
        send(
            writer,
            json!({ "type": "tool_execution_end", "toolCallId": id, "toolName": name,
            "result": { "content": [{ "type": "text", "text": text }], "details": details(name) },
            "isError": is_error }),
        );
    }
    send(
        writer,
        json!({ "type": "turn_end", "answer": { "message": tool_round(), "toolResults": [] } }),
    );
    // The answer comes later: the running turn's cache share shows meanwhile.
    std::thread::sleep(Duration::from_millis(1_500));
    send(writer, json!({ "type": "turn_start" }));
    send(
        writer,
        json!({ "type": "message_start", "message": answer(), "assistantMessageEvent": { "type": "start" } }),
    );
    send(
        writer,
        json!({ "type": "message_end", "message": answer() }),
    );
    send(
        writer,
        json!({ "type": "turn_end", "answer": { "message": answer(), "toolResults": [] } }),
    );
    send(writer, json!({ "type": "agent_end", "messages": [] }));
}

fn serve(listener: &UnixListener, messages: &Value) {
    listener.set_nonblocking(true).expect("nonblocking");
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
    stream.set_nonblocking(false).expect("blocking");
    let mut writer = stream.try_clone().expect("clones");
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
        let kind = envelope
            .pointer("/command/type")
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
            "attach" => write_json(
                &mut writer,
                &response(&id, "attach", &attach_data(messages)),
            ),
            "prompt" => {
                write_json(&mut writer, &response(&id, "prompt", &json!({})));
                stream_turn(&mut writer);
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

/// The frames of one session against the mock serving `messages` at
/// attach.
fn frames(messages: Value, steps: Vec<HeadlessStep>) -> Vec<String> {
    std::env::remove_var("TMUX");
    let dir = tempfile::TempDir::new().expect("temp dir");
    let socket = dir.path().join("tui.sock");
    let listener = UnixListener::bind(&socket).expect("binds");
    let handle = std::thread::spawn(move || serve(&listener, &messages));
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .expect("runtime");
    let plan = HeadlessPlan {
        steps,
        width: 100,
        height: 40,
    };
    let outcome = runtime
        .block_on(run_interactive(options(socket), UiMode::Headless(plan)))
        .expect("runs");
    drop(runtime);
    handle.join().expect("mock joins");
    outcome.frames
}

/// The frame's rows, trailing blanks cut.
fn rows(frame: &str) -> Vec<&str> {
    frame.lines().map(str::trim_end).collect()
}

#[test]
fn the_live_turn_ends_with_its_usage_footer_and_shows_its_cache_share_meanwhile() {
    let frames = frames(
        json!([]),
        vec![
            HeadlessStep::WaitMs(200),
            HeadlessStep::Submit("fix the greeting in hello.rs".to_string()),
            HeadlessStep::WaitRender {
                needle: "cache 90%".to_string(),
                timeout_ms: 10_000,
            },
            HeadlessStep::WaitIdle { timeout_ms: 10_000 },
            HeadlessStep::WaitRender {
                needle: "(95% hit)".to_string(),
                timeout_ms: 10_000,
            },
        ],
    );
    let running = frames
        .iter()
        .find(|frame| frame.contains("cache 90%"))
        .expect("a frame of the running turn shows its cache share");
    assert!(!running.contains("(95% hit)"), "{running}");
    let last = frames.last().expect("frames");
    let rows = rows(last);
    let footer = rows
        .iter()
        .position(|row| *row == FOOTER)
        .unwrap_or_else(|| panic!("the footer row:\n{last}"));
    assert_eq!(
        rows[footer - 1],
        "",
        "a blank row leads the footer:\n{last}"
    );
    let answer = rows
        .iter()
        .position(|row| row.contains("Fixed the greeting in src/hello.rs."))
        .expect("the answer");
    assert!(answer < footer, "{last}");
    assert!(failed_card(&rows), "the test run's card shows x:\n{last}");
    assert!(
        !last.contains("cache 9"),
        "the idle status line drops the share:\n{last}"
    );
    assert!(
        frames.iter().all(|frame| frame.is_ascii()),
        "every frame byte is ASCII, the status line's speed segment too:\n{last}"
    );
}

#[test]
fn a_reattach_folds_the_same_footer_from_the_stored_turn() {
    let frames = frames(
        stored_turn(),
        vec![HeadlessStep::WaitRender {
            needle: "(95% hit)".to_string(),
            timeout_ms: 10_000,
        }],
    );
    let last = frames.last().expect("frames");
    let rows = rows(last);
    let footer = rows.iter().position(|row| *row == FOOTER).expect("footer");
    assert!(failed_card(&rows), "the test run's card shows x:\n{last}");
    assert!(rows[..=footer].iter().all(|row| row.is_ascii()), "{last}");
    assert!(last.is_ascii(), "{last}");
}

/// The bash card marks the nonzero exit failed (`x`), the call the
/// footer's `1 failed` counts.
fn failed_card(rows: &[&str]) -> bool {
    rows.iter()
        .any(|row| row.trim_start().starts_with("x  bash"))
}
