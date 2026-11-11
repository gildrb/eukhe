//! Headless e2e for the session budget in the inline client: the status
//! line's `budget:` segment reads the attach snapshot's report, follows
//! every `budget_update`, and takes the tone of the phase; `/budget`
//! shows, sets, adds to and audits the budget through the daemon, and a
//! refusal of the daemon is the command's error row.
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

/// What the mock answers one budget command with, and the session events
/// it sends after the answer.
struct Reply {
    response: Result<Value, &'static str>,
    events: Vec<Value>,
}

fn write_json(writer: &mut UnixStream, value: &Value) {
    let mut line = serde_json::to_string(value).expect("serialize mock frame");
    line.push('\n');
    writer.write_all(line.as_bytes()).expect("write mock frame");
    writer.flush().expect("flush mock frame");
}

/// A budget report of `sess-1`: a cost limit and a limit of 50 tool
/// calls, 12 of them made.
fn report(limit_micros: u64, spent_micros: u64, phase: &str) -> Value {
    let mut report = json!({
        "sessionId": "sess-1",
        "limits": { "costMicros": limit_micros, "toolCalls": 50 },
        "free": {
            "costMicros": limit_micros - spent_micros,
            "tokens": 0,
            "timeMs": 0,
            "toolCalls": 38,
        },
        "held": { "costMicros": 0, "tokens": 0, "timeMs": 0, "toolCalls": 0 },
        "spent": { "costMicros": spent_micros, "tokens": 0, "timeMs": 0, "toolCalls": 12 },
        "lent": { "costMicros": 0, "tokens": 0, "timeMs": 0, "toolCalls": 0 },
        "over": { "costMicros": 0, "tokens": 0, "timeMs": 0, "toolCalls": 0 },
        "phase": phase,
    });
    if phase != "working" {
        report["short"] = json!("cost");
    }
    report
}

fn budget_update(budget: &Value) -> Value {
    json!({ "type": "budget_update", "budget": budget })
}

/// The mock supervisor: the hello, `attach` (the snapshot's state carries
/// `budget`), the scripted answer to each budget command, and an empty
/// success for everything else. Returns the budget commands it received.
fn serve(
    listener: &UnixListener,
    budget: &Value,
    answer: impl Fn(&Value) -> Option<Reply>,
) -> Vec<Value> {
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
    let mut received = Vec::new();
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
        let command_type = command["type"].as_str().unwrap_or_default();
        let reply = match answer(command) {
            Some(reply) => {
                received.push(command.clone());
                reply
            }
            None => Reply {
                response: Ok(if command_type == "attach" {
                    attach_data(budget)
                } else {
                    json!({})
                }),
                events: Vec::new(),
            },
        };
        let mut response = json!({
            "type": "response",
            "id": id,
            "command": command_type,
            "success": reply.response.is_ok(),
        });
        match reply.response {
            Ok(data) => response["data"] = data,
            Err(error) => response["error"] = json!(error),
        }
        write_json(&mut writer, &response);
        for event in &reply.events {
            write_json(
                &mut writer,
                &json!({
                    "type": "session_event",
                    "activeSessionId": "s1",
                    "event": event,
                }),
            );
        }
    }
    received
}

fn attach_data(budget: &Value) -> Value {
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
                "model": "faux-1",
                "isStreaming": false,
                "isCompacting": false,
                "budget": budget,
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

/// Run `steps` against the mock; the captured frames and the budget
/// commands the mock received.
fn run(
    budget: Value,
    answer: impl Fn(&Value) -> Option<Reply> + Send + 'static,
    steps: Vec<HeadlessStep>,
) -> (Vec<String>, Vec<Value>) {
    std::env::remove_var("TMUX");
    let dir = tempfile::TempDir::new().expect("temp dir");
    let socket = dir.path().join("tui.sock");
    let listener = UnixListener::bind(&socket).expect("bind mock socket");
    let handle = std::thread::spawn(move || serve(&listener, &budget, answer));
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .expect("tokio runtime");
    let plan = HeadlessPlan {
        steps,
        width: 120,
        height: 30,
    };
    let frames = runtime
        .block_on(run_interactive(options(socket), UiMode::Headless(plan)))
        .expect("interactive run")
        .frames;
    let received = handle.join().expect("mock supervisor finished");
    (frames, received)
}

fn submit(text: &str) -> HeadlessStep {
    HeadlessStep::Submit(text.to_string())
}

fn wait(needle: &str) -> HeadlessStep {
    HeadlessStep::WaitRender {
        needle: needle.to_string(),
        timeout_ms: 10_000,
    }
}

/// The status line of each frame that has one (its row that names the
/// model), oldest first.
fn status_lines(frames: &[String]) -> Vec<&str> {
    frames
        .iter()
        .filter_map(|frame| frame.lines().rev().find(|line| line.contains("[M] faux-1")))
        .collect()
}

/// A session with a budget: the status line reads the snapshot's report,
/// then each `budget_update`; `/budget add` and `/budget audit` go to the
/// daemon and show its answer; a refused `/budget set` is the error row.
#[test]
fn the_status_line_follows_the_budget_and_the_command_changes_it() {
    let answer = |command: &Value| match command["type"].as_str() {
        // The answer carries the added budget; the update after it a
        // request that settled meanwhile.
        Some("add_budget") => Some(Reply {
            response: Ok(json!({ "budget": report(3_000_000, 420_000, "working") })),
            events: vec![budget_update(&report(3_000_000, 500_000, "working"))],
        }),
        Some("audit_budget") => Some(Reply {
            response: Ok(json!({
                "audit": {
                    "records": 14,
                    "settled": { "costMicros": 500_000, "tokens": 0, "timeMs": 0, "toolCalls": 12 },
                    "spent": { "costMicros": 500_000, "tokens": 0, "timeMs": 0, "toolCalls": 12 },
                    "exact": true,
                    "firstMismatch": null,
                },
            })),
            events: Vec::new(),
        }),
        Some("set_budget") => Some(Reply {
            response: Err("session sess-1 already has a budget"),
            events: vec![budget_update(&report(3_000_000, 500_000, "wrap_up"))],
        }),
        Some(_) | None => None,
    };
    let (frames, received) = run(
        report(2_000_000, 420_000, "working"),
        answer,
        vec![
            wait("budget: $0.42/$2.00 - 12/50 calls"),
            submit("/budget add cost=1"),
            wait("budget: $0.50/$3.00 - 12/50 calls"),
            submit("/budget audit"),
            wait("ledger exact: 14 records, settled $0.50, 12 calls"),
            submit("/budget set cost=5"),
            wait("session sess-1 already has a budget"),
            wait("12/50 calls - wrap-up"),
            HeadlessStep::WaitIdle { timeout_ms: 10_000 },
        ],
    );
    let all = frames.join("\n---frame---\n");
    let seen = |needle: &str| frames.iter().any(|frame| frame.contains(needle));
    let status = status_lines(&frames);
    assert_eq!(
        (
            status
                .first()
                .map(|line| line.contains("budget: $0.42/$2.00 - 12/50 calls")),
            // The answer of `/budget add` is its row in the transcript.
            seen("budget: $0.42/$3.00 - 12/50 calls"),
            status
                .last()
                .map(|line| line.contains("budget: $0.50/$3.00 - 12/50 calls - wrap-up")),
            received,
        ),
        (
            Some(true),
            true,
            Some(true),
            vec![
                json!({
                    "type": "add_budget",
                    "activeSessionId": "s1",
                    "amounts": { "costMicros": 1_000_000, "tokens": 0, "timeMs": 0, "toolCalls": 0, "requests": 0 },
                }),
                json!({ "type": "audit_budget", "activeSessionId": "s1" }),
                json!({
                    "type": "set_budget",
                    "activeSessionId": "s1",
                    "limits": { "costMicros": 5_000_000 },
                }),
            ],
        ),
        "frames:\n{all}"
    );
}

/// A session without a budget: no segment and `no budget set`; `/budget
/// set` gives it one, which the status line then shows; a value that does
/// not parse is refused in the client and never sent.
#[test]
fn a_session_without_a_budget_gets_one_from_the_command() {
    let answered = json!({
        "sessionId": "sess-1",
        "limits": { "costMicros": 2_000_000, "tokens": 200_000 },
        "free": { "costMicros": 2_000_000, "tokens": 200_000, "timeMs": 0, "toolCalls": 0 },
        "phase": "working",
    });
    let answer = move |command: &Value| match command["type"].as_str() {
        Some("get_budget") => Some(Reply {
            response: Ok(json!({ "budget": null })),
            events: Vec::new(),
        }),
        Some("set_budget") => Some(Reply {
            response: Ok(json!({ "budget": answered })),
            events: vec![budget_update(&answered)],
        }),
        Some(_) | None => None,
    };
    let (frames, received) = run(
        Value::Null,
        answer,
        vec![
            wait("[M] faux-1"),
            submit("/budget"),
            wait("no budget set"),
            submit("/budget set cost=abc"),
            wait("cost \"abc\": expected dollars, like 1.50 or $1.50"),
            submit("/budget set cost=2 tokens=200k"),
            wait("budget: $0.00/$2.00 - 0/200k tok"),
            HeadlessStep::WaitIdle { timeout_ms: 10_000 },
        ],
    );
    let all = frames.join("\n---frame---\n");
    let status = status_lines(&frames);
    assert_eq!(
        (
            status.first().map(|line| line.contains("budget:")),
            status
                .last()
                .map(|line| line.contains("budget: $0.00/$2.00 - 0/200k tok")),
            received,
        ),
        (
            Some(false),
            Some(true),
            vec![
                json!({ "type": "get_budget", "activeSessionId": "s1" }),
                json!({
                    "type": "set_budget",
                    "activeSessionId": "s1",
                    "limits": { "costMicros": 2_000_000, "tokens": 200_000 },
                }),
            ],
        ),
        "frames:\n{all}"
    );
}
