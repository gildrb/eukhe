//! Headless e2e for the Escape interrupt (robustness findings F2-F4),
//! matched to omp's `handleEscape` (input-controller.ts:629-682): a double
//! Escape during a stream stops the turn and never opens the session tree
//! over the next prompt (F2); Escape returns the user's parked messages to
//! the editor instead of starting the turn the user just stopped (F3,
//! `restoreQueuedMessagesToEditor({ abort: true })`); and a run stopped
//! during its tools says "Operation aborted", not "ended without a reply"
//! (F4). Each test replays a run against the real interactive loop and a
//! scripted mock daemon that waits for the client's requests.

use std::io::{BufRead, BufReader, Write};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::PathBuf;
use std::sync::{mpsc, Arc, Mutex};
use std::time::Duration;

use crossterm::event::{KeyCode, KeyEvent, KeyModifiers};
use eukhe_tui::interactive::{
    run_interactive, HeadlessPlan, HeadlessStep, InteractiveOptions, ModelSelection,
    SessionSelection, UiMode,
};
use serde_json::{json, Value};

/// The prompt every test submits.
const PROMPT: &str = "go now";
/// The streamed partial reply the interrupt stops.
const PARTIAL: &str = "streaming partial words";
/// The row a turn that ended with no reply leaves.
const NO_REPLY: &str = "The turn ended without a reply";
/// The row of a stopped turn.
const ABORTED: &str = "Operation aborted";
/// The tree selector's title row.
const TREE_PANE: &str = "Session Tree";

/// One step of the mock daemon, in order.
enum Act {
    /// Wait for the client's prompt carrying this text and admit it.
    Prompt(&'static str),
    /// Wait for the client's request of this command type.
    Await(&'static str),
    /// One session event.
    Event(Value),
}

/// One client request the script may wait on: its type, id, and command.
type Request = (String, String, Value);

fn write(writer: &Mutex<UnixStream>, value: &Value) {
    let mut line = serde_json::to_string(value).expect("serialize mock frame");
    line.push('\n');
    let mut writer = writer.lock().expect("mock writer");
    let _ = writer.write_all(line.as_bytes());
    let _ = writer.flush();
}

fn response(id: &str, command: &str, data: &Value) -> Value {
    json!({ "type": "response", "id": id, "command": command, "success": true, "data": data })
}

fn session_event(event: &Value) -> Value {
    json!({ "type": "session_event", "activeSessionId": "s1", "event": event })
}

/// The queue projection with `steering` parked by the user.
fn queue_update(steering: &[&str]) -> Value {
    let steering: Vec<Value> = steering
        .iter()
        .map(|text| json!({ "text": text, "origin": { "kind": "user" } }))
        .collect();
    json!({
        "type": "session_action_update",
        "actions": { "queuedCount": steering.len(), "steering": steering, "followUps": [] },
    })
}

fn attach_response(id: &str) -> Value {
    response(
        id,
        "attach",
        &json!({
            "protocol": { "name": "eukhe.daemon", "version": 7 },
            "activeSessionId": "s1",
            "snapshot": {
                "activeSessionId": "s1",
                "summary": { "id": "s1", "cwd": "/tmp" },
                "state": {
                    "activeSessionId": "s1",
                    "cwd": "/tmp",
                    "sessionId": "sess-1",
                    "sessionName": "escape interrupt",
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
        }),
    )
}

/// The session tree with two entries, so a tree the client asks for
/// mounts (an empty answer only notes "No entries in session").
fn tree_response(id: &str) -> Value {
    response(
        id,
        "get_session_tree",
        &json!({
            "flatNodes": [
                {
                    "entry": {
                        "type": "message",
                        "id": "n0",
                        "parentId": null,
                        "timestamp": "2024-01-01T00:00:00.000Z",
                        "message": { "role": "user", "content": PROMPT, "timestamp": 0 },
                    },
                },
                {
                    "entry": {
                        "type": "message",
                        "id": "n1",
                        "parentId": "n0",
                        "timestamp": "2024-01-01T00:00:01.000Z",
                        "message": {
                            "role": "assistant",
                            "content": [{ "type": "text", "text": PARTIAL }],
                            "api": "scripted",
                            "provider": "scripted",
                            "model": "faux-1",
                            "usage": {
                                "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 0,
                                "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
                            },
                            "stopReason": "aborted",
                            "timestamp": 1,
                        },
                    },
                },
            ],
            "leafId": "n1",
        }),
    )
}

/// Answer the client's requests until it disconnects and hand each to the
/// script: the prompt's answer is the script's; a queued-message delete
/// applies (the queue update follows); the tree request gets the
/// two-entry tree; everything else is an empty success.
fn serve_requests(
    stream: UnixStream,
    writer: &Mutex<UnixStream>,
    requests: &mpsc::Sender<Request>,
) {
    let mut reader = BufReader::new(stream);
    let mut line = String::new();
    loop {
        line.clear();
        match reader.read_line(&mut line) {
            Ok(0) | Err(_) => return,
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
            "create" => write(
                writer,
                &response(
                    &id,
                    "create",
                    &json!({
                        "activeSessionId": "s1",
                        "id": "s1",
                        "sessionId": "sess-1",
                        "sessionFile": "/tmp/sess-1.jsonl",
                    }),
                ),
            ),
            "attach" => write(writer, &attach_response(&id)),
            "get_session_tree" => write(writer, &tree_response(&id)),
            "prompt" => {}
            "mutate_queued_message" => {
                write(
                    writer,
                    &response(&id, &kind, &json!({ "status": "applied" })),
                );
                write(writer, &session_event(&queue_update(&[])));
            }
            _ => write(writer, &response(&id, &kind, &json!({}))),
        }
        let _ = requests.send((kind, id, command));
    }
}

/// The next request of type `kind` (earlier ones of other types pass).
fn next_request(requests: &mpsc::Receiver<Request>, kind: &str) -> Request {
    loop {
        let request = requests
            .recv_timeout(Duration::from_secs(10))
            .unwrap_or_else(|_| panic!("the client never sent `{kind}`"));
        if request.0 == kind {
            return request;
        }
    }
}

/// Serve one client: greet it, answer its requests, and play `script`.
fn serve(listener: &UnixListener, script: Vec<Act>) {
    let (stream, _) = listener.accept().expect("the client connects");
    let writer = Arc::new(Mutex::new(stream.try_clone().expect("clone mock socket")));
    write(
        &writer,
        &json!({
            "type": "daemon_hello",
            "protocol": { "name": "eukhe.daemon", "version": 7 },
            "serverCapabilities": ["abort_and_send_queued"],
            "clientId": "mock",
        }),
    );
    let (requests_tx, requests) = mpsc::channel();
    let request_loop = {
        let writer = Arc::clone(&writer);
        std::thread::spawn(move || serve_requests(stream, &writer, &requests_tx))
    };
    for act in script {
        match act {
            Act::Prompt(text) => {
                let (_, id, command) = next_request(&requests, "prompt");
                assert_eq!(
                    command.get("message").and_then(Value::as_str),
                    Some(text),
                    "the client's prompt"
                );
                write(&writer, &response(&id, "prompt", &json!({})));
            }
            Act::Await(kind) => {
                next_request(&requests, kind);
            }
            Act::Event(event) => write(&writer, &session_event(&event)),
        }
    }
    request_loop.join().expect("mock request loop");
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

/// Submit the prompt, play `script` on the daemon side, run `steps`, and
/// return every rendered frame.
fn run(script: Vec<Act>, steps: Vec<HeadlessStep>) -> Vec<String> {
    // The ambient TMUX variable adds a startup notice to the transcript.
    std::env::remove_var("TMUX");
    let dir = tempfile::TempDir::new().expect("temp dir");
    let socket = dir.path().join("tui.sock");
    let listener = UnixListener::bind(&socket).expect("bind mock socket");
    let daemon = std::thread::spawn(move || serve(&listener, script));
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .expect("tokio runtime");
    let mut plan = vec![HeadlessStep::Submit(PROMPT.to_string())];
    plan.extend(steps);
    let outcome = runtime
        .block_on(run_interactive(
            options(socket),
            UiMode::Headless(HeadlessPlan {
                steps: plan,
                width: 140,
                height: 40,
            }),
        ))
        .expect("the interactive run settles (no turn stays active)");
    daemon.join().expect("the mock daemon played its script");
    outcome.frames
}

fn wait_for(needle: &str) -> HeadlessStep {
    HeadlessStep::WaitRender {
        needle: needle.to_string(),
        timeout_ms: 5_000,
    }
}

fn key(code: KeyCode) -> HeadlessStep {
    HeadlessStep::Key(KeyEvent::new(code, KeyModifiers::NONE))
}

fn all_frames(frames: &[String]) -> String {
    frames.join("\n=====\n")
}

fn user(text: &str) -> Value {
    json!({ "role": "user", "content": [{ "type": "text", "text": text }], "timestamp": 1 })
}

fn assistant(content: &Value, stop_reason: &str, error: Option<&str>) -> Value {
    let mut message = json!({
        "role": "assistant",
        "content": content,
        "api": "faux",
        "provider": "faux",
        "model": "faux-1",
        "usage": {
            "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 0,
            "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
        },
        "stopReason": stop_reason,
        "timestamp": 1,
    });
    if let Some(error) = error {
        message["errorMessage"] = json!(error);
    }
    message
}

fn text(text: &str) -> Value {
    json!([{ "type": "text", "text": text }])
}

fn ev(kind: &str) -> Act {
    Act::Event(json!({ "type": kind }))
}

/// A run starts for `prompt`: its turn and its user message.
fn run_for(prompt: &str) -> Vec<Act> {
    let message = user(prompt);
    vec![
        ev("agent_start"),
        ev("turn_start"),
        Act::Event(json!({ "type": "message_start", "message": message })),
        Act::Event(json!({ "type": "message_end", "message": message })),
    ]
}

/// The assistant message `message` opens (streaming).
fn message_start(message: &Value) -> Act {
    Act::Event(json!({
        "type": "message_start",
        "message": message,
        "assistantMessageEvent": { "type": "start" },
    }))
}

fn message_end(message: &Value) -> Act {
    Act::Event(json!({ "type": "message_end", "message": message }))
}

fn turn_end(message: &Value) -> Act {
    Act::Event(json!({ "type": "turn_end", "message": message, "toolResults": [] }))
}

fn run_end() -> Act {
    Act::Event(json!({ "type": "agent_end", "messages": [] }))
}

/// The stream stops: the partial reply settles aborted, the turn and the
/// run end.
fn stopped_stream() -> Vec<Act> {
    let aborted = assistant(&text(PARTIAL), "aborted", Some("Request was aborted"));
    vec![message_end(&aborted), turn_end(&aborted), run_end()]
}

/// F2: Escape twice during a stream stops the turn; the second press
/// never opens the session tree, so the next typed prompt is sent (it
/// used to land in the tree's search box and never reach the daemon).
#[test]
fn a_double_escape_during_a_stream_stops_it_and_the_next_prompt_sends() {
    let mut script = vec![Act::Prompt(PROMPT)];
    script.extend(run_for(PROMPT));
    script.push(message_start(&assistant(&text(PARTIAL), "stop", None)));
    script.push(Act::Await("abort_and_send_queued"));
    script.extend(stopped_stream());
    script.push(Act::Prompt("ping two"));
    script.extend(run_for("ping two"));
    let answer = assistant(&text("pong answer"), "stop", None);
    script.extend([
        message_start(&answer),
        message_end(&answer),
        turn_end(&answer),
        run_end(),
    ]);
    let steps = vec![
        wait_for(PARTIAL),
        key(KeyCode::Esc),
        HeadlessStep::WaitMs(150),
        key(KeyCode::Esc),
        wait_for(ABORTED),
        HeadlessStep::WaitMs(300),
        HeadlessStep::Type("ping two".to_string()),
        key(KeyCode::Enter),
        wait_for("pong answer"),
        HeadlessStep::WaitMs(300),
    ];
    let frames = run(script, steps);
    assert!(
        frames.iter().all(|frame| !frame.contains(TREE_PANE)),
        "the interrupt never opens the tree:\n{}",
        all_frames(&frames)
    );
    let last = frames.last().expect("a final frame");
    assert!(last.contains("pong answer"), "the next prompt ran:\n{last}");
}

/// F3: Escape with a steering message parked behind the stream withdraws
/// it into the editor instead of sending it as a new turn: the script
/// only goes on once the client deleted the parked message, and no turn
/// runs for it.
#[test]
fn escape_returns_the_parked_steering_message_to_the_editor() {
    let mut script = vec![Act::Prompt(PROMPT)];
    script.extend(run_for(PROMPT));
    script.push(message_start(&assistant(&text(PARTIAL), "stop", None)));
    script.push(Act::Prompt("steer msg"));
    script.push(Act::Event(queue_update(&["steer msg"])));
    script.push(Act::Await("mutate_queued_message"));
    script.push(Act::Await("abort_and_send_queued"));
    script.extend(stopped_stream());
    let steps = vec![
        wait_for(PARTIAL),
        HeadlessStep::Submit("steer msg".to_string()),
        wait_for("Steering"),
        key(KeyCode::Esc),
        wait_for(ABORTED),
        HeadlessStep::WaitMs(500),
    ];
    let frames = run(script, steps);
    let last = frames.last().expect("a final frame");
    assert!(
        !last.contains("Steering"),
        "the parked message left the queue:\n{last}"
    );
    assert!(
        last.lines()
            .any(|line| line.trim_start().starts_with('>') && line.contains("steer msg")),
        "the parked message is back in the editor:\n{last}"
    );
}

/// F4: Escape while a tool runs stops the run, which ends with no
/// answering turn: the chat says the operation was aborted, not that the
/// turn ended without a reply.
#[test]
fn escape_during_a_tool_says_the_operation_was_aborted() {
    let tools = assistant(
        &json!([
            { "type": "text", "text": "listing files" },
            { "type": "toolCall", "id": "c1", "name": "bash", "arguments": { "script": "sleep 45" } },
        ]),
        "toolUse",
        None,
    );
    let mut script = vec![Act::Prompt(PROMPT)];
    script.extend(run_for(PROMPT));
    script.extend([message_start(&tools), message_end(&tools)]);
    script.push(Act::Event(json!({
        "type": "tool_execution_start",
        "toolCallId": "c1",
        "toolName": "bash",
        "args": { "script": "sleep 45" },
    })));
    script.push(Act::Await("abort_and_send_queued"));
    script.push(Act::Event(json!({
        "type": "tool_execution_end",
        "toolCallId": "c1",
        "toolName": "bash",
        "result": { "content": [{ "type": "text", "text": "Tool bash was aborted" }] },
        "isError": true,
    })));
    script.extend([turn_end(&tools), run_end()]);
    let steps = vec![
        wait_for("listing files"),
        key(KeyCode::Esc),
        wait_for(ABORTED),
        HeadlessStep::WaitMs(300),
    ];
    let frames = run(script, steps);
    let last = frames.last().expect("a final frame");
    assert!(last.contains(ABORTED), "the stop shows:\n{last}");
    assert!(
        !last.contains(NO_REPLY),
        "a stopped run is not a turn without a reply:\n{last}"
    );
}
