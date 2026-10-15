//! Headless e2e for the chat memory in the inline client: the status
//! line's `mem` gauge seeds from the open-time `get_memory`, `/memory`
//! opens the memory tree (the status header and one dated, labelled row
//! per view line), Right drills a one-message line down to its message
//! and a summary line down to its two halves, a pushed `memory_update`
//! lands as a live row (no turn running) and moves the gauge, and
//! arguments answer the usage.
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

const HEADER: &str = " memory: 43 messages, view 87.2 KB / 128.0 KB (floor 64.0 KB), 2 lines, \
                      2 unsummarized, 1 compaction running, model anthropic/claude-haiku-4-5";

/// The two pushed summaries, coalesced into one live row.
const LIVE_ROW: &str = "memory: summarized 41+1, 42+1, 40+2 (view 91.0 KB)";

const OCT_1: &str = "2026-10-01T09:00:00.000+02:00";
const OCT_2: &str = "2026-10-02T10:00:00.000+02:00";
const OCT_3: &str = "2026-10-03T08:00:00.000+02:00";

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

fn tree_node(
    (id, count): (u64, u64),
    (first, last): (&str, &str),
    kinds: &Value,
    summary: &Value,
) -> Value {
    json!({
        "id": id,
        "count": count,
        "firstDate": first,
        "lastDate": last,
        "kinds": kinds,
        "summary": summary,
    })
}

/// One `get_memory_tree` level: the view's two lines, the two halves of
/// `0+32`, or the message under `32+1`.
fn tree_level(node: &Value) -> Value {
    let level = if node.is_null() {
        json!({ "kind": "lines", "nodes": [
            tree_node(
                (0, 32),
                (OCT_1, OCT_2),
                &json!([{ "kind": "user", "count": 20 }, { "kind": "talk", "count": 12 }]),
                &json!("user: hi | bot: hello\nthen the release plan"),
            ),
            tree_node((32, 1), (OCT_3, OCT_3), &json!([{ "kind": "user", "count": 1 }]), &Value::Null),
        ] })
    } else if *node == json!({ "id": 0, "count": 32 }) {
        json!({ "kind": "lines", "nodes": [
            tree_node(
                (0, 16),
                (OCT_1, "2026-10-01T18:00:00.000+02:00"),
                &json!([{ "kind": "user", "count": 10 }, { "kind": "talk", "count": 6 }]),
                &json!("user: hi"),
            ),
            tree_node(
                (16, 16),
                ("2026-10-02T08:00:00.000+02:00", OCT_2),
                &json!([{ "kind": "user", "count": 10 }, { "kind": "talk", "count": 6 }]),
                &json!("bot: hello"),
            ),
        ] })
    } else {
        assert_eq!(*node, json!({ "id": 32, "count": 1 }), "an unexpected line");
        json!({ "kind": "message", "message": {
            "id": 32,
            "kind": "user",
            "date": OCT_3,
            "text": "plan the release\nthen ship it",
        } })
    };
    json!({ "tree": { "status": status(), "node": node, "level": level } })
}

/// Serve one connection: the hello (with the `memory` and `memory_tree`
/// lanes), the attach snapshot, the open-time `get_memory` status,
/// `get_memory_tree` (the `0+32` expansion followed by two pushed
/// `memory_update`s), and an empty success for everything else.
fn serve(listener: &UnixListener) {
    let (stream, _) = listener.accept().expect("accept");
    let mut writer = stream.try_clone().expect("clone mock socket");
    let mut reader = BufReader::new(stream);
    write_json(
        &mut writer,
        &json!({
            "type": "daemon_hello",
            "protocol": { "name": "eukhe.daemon", "version": 7 },
            "serverCapabilities": ["memory", "memory_tree"],
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
        let expanded =
            command_type == "get_memory_tree" && command["node"] == json!({ "id": 0, "count": 32 });
        let data = match command_type.as_str() {
            "attach" => attach_data(),
            "get_memory" => {
                assert_eq!(command["zoom"], Value::Null);
                json!({ "memory": { "status": status(), "text": "0+32|user: hi\n32+1|plan" } })
            }
            "get_memory_tree" => {
                assert_eq!(command["activeSessionId"], "s1");
                tree_level(&command["node"])
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
        if expanded {
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
    }
}

fn key(code: KeyCode) -> HeadlessStep {
    HeadlessStep::Key(KeyEvent::new(code, KeyModifiers::NONE))
}

/// The tree's rows in `frame`: the rows between the status header's blank
/// and the key hint, trailing padding trimmed.
fn tree_rows(frame: &str) -> Vec<String> {
    let lines: Vec<&str> = frame.lines().map(str::trim_end).collect();
    let header = lines
        .iter()
        .position(|line| *line == HEADER)
        .expect("the tree's header");
    lines[header + 2..]
        .iter()
        .take_while(|line| !line.contains(" move - "))
        .map(|line| (*line).to_string())
        .collect()
}

#[test]
fn memory_opens_the_tree_drills_down_and_shows_live_updates() {
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
            wait("> + 32+1  2026-10-03 08:00  user 1  (not summarized yet)"),
            // The newest line holds one message: Right opens it whole.
            key(KeyCode::Right),
            wait("    then ship it"),
            // Up to the summary line, whose halves Right fetches.
            key(KeyCode::Up),
            key(KeyCode::Right),
            wait("+ 16+16"),
            // The update pushed after the expansion: a live row while no
            // turn runs; Esc closes the tree and the gauge follows it.
            wait(LIVE_ROW),
            key(KeyCode::Esc),
            HeadlessStep::WaitGone {
                needle: HEADER.to_string(),
                timeout_ms: 10_000,
            },
            wait("mem 91/128K"),
            HeadlessStep::Submit("/memory zoom 40".to_string()),
            wait("Usage: /memory"),
        ],
        width: 200,
        height: 40,
    };
    let frames = runtime
        .block_on(run_interactive(options(socket), UiMode::Headless(plan)))
        .expect("interactive run")
        .frames;
    handle.join().expect("mock supervisor finished");
    let all = || frames.join("\n---frame---\n");
    let view = frames
        .iter()
        .find(|frame| frame.contains("> + 32+1"))
        .unwrap_or_else(|| panic!("the view's rows:\n{}", all()));
    assert_eq!(
        tree_rows(view),
        vec![
            "  + 0+32  2026-10-01 09:00 -> 10-02 10:00  user 20, talk 12  user: hi | bot: hello",
            "> + 32+1  2026-10-03 08:00  user 1  (not summarized yet)",
        ]
    );
    let expanded = frames
        .iter()
        .rev()
        .find(|frame| frame.contains("+ 16+16"))
        .unwrap_or_else(|| panic!("the expanded tree:\n{}", all()));
    assert_eq!(
        tree_rows(expanded),
        vec![
            "> - 0+32  2026-10-01 09:00 -> 10-02 10:00  user 20, talk 12  user: hi | bot: hello",
            "      user: hi | bot: hello",
            "      then the release plan",
            "    + 0+16  2026-10-01 09:00 -> 18:00  user 10, talk 6  user: hi",
            "    + 16+16  2026-10-02 08:00 -> 10:00  user 10, talk 6  bot: hello",
            "  - 32+1  2026-10-03 08:00  user 1  (not summarized yet)",
            "    user  2026-10-03 08:00",
            "    plan the release",
            "    then ship it",
        ]
    );
    assert!(
        frames
            .iter()
            .all(|frame| !frame.contains("memory: summarized 40+2")),
        "the second update folds into the live row, never a row of its own:\n{}",
        all()
    );
}
