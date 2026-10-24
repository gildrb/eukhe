//! Headless e2e for the pinned agents block: a running subagent shows
//! above the composer with its model, reasoning level, phase, current
//! tool, context use, and spend, straight from the roster the client
//! subscribed to; when a roster push says it stopped, the block goes. A
//! collapsed block names the keys that expand it from where the keys go.
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

/// The session's one subagent: running a tool while `running`, idle
/// after.
fn worker(running: bool) -> Value {
    let mut summary = json!({
        "sessionId": "c1",
        "activeSessionId": "c1-live",
        "sessionName": "worker-1",
        "runtimeKind": "subagent",
        "rlmChildId": "sub-c1",
        "rlmDepth": 1,
        "parentActiveSessionId": "s1",
        "parentSessionId": "sess-1",
        "model": { "id": "elpis/qwen3.8-27b" },
        "thinkingLevel": "high",
        "usage": { "cost": 0.25 },
        "contextUsage": { "tokens": 64_000, "contextWindow": 128_000, "percent": 50.0 },
    });
    if running {
        summary["isStreaming"] = json!(true);
        summary["isRunningTools"] = json!(true);
        summary["currentTool"] = json!({ "name": "bash" });
    }
    json!({
        "agentId": "c1",
        "status": if running { "running" } else { "idle" },
        "summary": summary,
    })
}

/// The lead session's roster row, then `children`.
fn roster(children: impl IntoIterator<Item = Value>) -> Value {
    let mut rows = vec![json!({
        "agentId": "s1",
        "status": "idle",
        "summary": {
            "sessionId": "sess-1",
            "activeSessionId": "s1",
            "sessionName": "lead",
            "runtimeKind": "top-level",
        },
    })];
    rows.extend(children);
    Value::Array(rows)
}

/// One more running subagent, `worker-<n>`.
fn helper(n: u32) -> Value {
    let mut row = worker(true);
    row["agentId"] = json!(format!("c{n}"));
    row["summary"]["sessionId"] = json!(format!("c{n}"));
    row["summary"]["activeSessionId"] = json!(format!("c{n}-live"));
    row["summary"]["sessionName"] = json!(format!("worker-{n}"));
    row["summary"]["rlmChildId"] = json!(format!("sub-c{n}"));
    row
}

/// Serve one connection: the hello, the attach snapshot, `roster`, and an
/// empty success for everything else; the message to `worker-1` is
/// followed by the roster push that settles it.
fn serve(listener: &UnixListener, roster: &Value) {
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
        let data = match command_type.as_str() {
            "attach" => attach_data(),
            "roster_subscribe" => json!({ "roster": roster }),
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
        if command_type == "prompt" && command["activeSessionId"] == "c1-live" {
            write_json(
                &mut writer,
                &json!({ "type": "roster_update", "changed": [worker(false)], "removed": [] }),
            );
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
                "sessionName": "lead",
                "model": "faux-1",
                "isStreaming": false,
                "isCompacting": false,
                "sessionActions": { "queuedCount": 0, "steering": [], "followUps": [] },
            },
            "messages": [
                { "role": "user", "content": "hello", "timestamp": 1 },
                {
                    "role": "assistant",
                    "content": [{ "type": "text", "text": "settled answer" }],
                    "api": "scripted",
                    "provider": "scripted",
                    "model": "faux-1",
                    "usage": {
                        "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 0,
                        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
                    },
                    "stopReason": "stop",
                    "timestamp": 2,
                },
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

#[test]
fn a_running_subagent_shows_in_the_block_until_it_stops() {
    std::env::remove_var("TMUX");
    let dir = tempfile::TempDir::new().expect("temp dir");
    let socket = dir.path().join("tui.sock");
    let listener = UnixListener::bind(&socket).expect("bind mock socket");
    let handle = std::thread::spawn(move || serve(&listener, &roster([worker(true)])));
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
            wait("settled answer"),
            // The block heads the dock with the worker's live row.
            wait("Agents  1 running"),
            wait("`- worker-1  qwen3.8-27b:high  Executing - "),
            wait("-> bash  ctx 64k/128k 50%  $0.25"),
            // The message ends the worker's run: the roster push says it
            // is idle, and the block goes.
            HeadlessStep::Submit("@worker-1 wrap up".to_string()),
            wait("you -> worker-1: wrap up"),
            HeadlessStep::WaitGone {
                needle: "Agents  1 running".to_string(),
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
    handle.join().expect("mock supervisor finished");
    assert!(
        frames
            .iter()
            .all(|frame| !frame.contains("timed out waiting")),
        "every render condition held:\n{}",
        frames.join("\n---frame---\n")
    );
    let last = frames.last().expect("a frame");
    assert!(
        !last.contains("worker-1  qwen3.8-27b:high"),
        "the block is gone once nothing runs:\n{last}"
    );
}

fn key(code: KeyCode, modifiers: KeyModifiers) -> HeadlessStep {
    HeadlessStep::Key(KeyEvent::new(code, modifiers))
}

/// The user's case: five running subagents fold to three rows and "2
/// more". From the editor (a draft in it) Space is text, so the row names
/// the focus key first; once the dock holds the focus, Space expands.
/// Before the fix the row said `space: expand` from the editor too, where
/// Space only typed a space.
#[test]
fn the_collapsed_block_names_keys_that_expand_it() {
    std::env::remove_var("TMUX");
    let dir = tempfile::TempDir::new().expect("temp dir");
    let socket = dir.path().join("tui.sock");
    let listener = UnixListener::bind(&socket).expect("bind mock socket");
    let handle = std::thread::spawn(move || {
        serve(
            &listener,
            &roster([worker(true), helper(2), helper(3), helper(4), helper(5)]),
        );
    });
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
            wait("Agents  5 running"),
            wait("... 2 more (Alt+A, Space: expand)"),
            key(KeyCode::Char('h'), KeyModifiers::NONE),
            key(KeyCode::Char(' '), KeyModifiers::NONE),
            key(KeyCode::Char('i'), KeyModifiers::NONE),
            wait("> h i"),
            wait("... 2 more (Alt+A, Space: expand)"),
            key(KeyCode::Char('a'), KeyModifiers::ALT),
            wait("... 2 more (Space: expand)"),
            key(KeyCode::Char(' '), KeyModifiers::NONE),
            HeadlessStep::WaitGone {
                needle: "2 more".to_string(),
                timeout_ms: 10_000,
            },
            wait("worker-5"),
        ],
        width: 160,
        height: 40,
    };
    let frames = runtime
        .block_on(run_interactive(options(socket), UiMode::Headless(plan)))
        .expect("interactive run")
        .frames;
    handle.join().expect("mock supervisor finished");
    assert!(
        frames
            .iter()
            .all(|frame| !frame.contains("timed out waiting")),
        "every render condition held:\n{}",
        frames.join("\n---frame---\n")
    );
}
