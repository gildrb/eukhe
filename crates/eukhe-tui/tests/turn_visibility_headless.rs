//! Headless e2e for `laws/turn_visibility.bend`'s findings F1-F16: "it must
//! always be obvious when eukhe is working; a prompt that returns nothing
//! can never happen". Each test replays a finding's event history against
//! the real interactive loop -- a scripted mock daemon answers the prompt,
//! streams the session events, closes the session or replaces its worker
//! (the client re-attaches and rebuilds the chat from the snapshot) -- and
//! checks the rendered frames: the working indicator is up exactly while
//! work runs, and a turn that ends without an answer leaves exactly one
//! row that says so and names the next step.

use std::io::{BufRead, BufReader, Write};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::PathBuf;
use std::sync::mpsc;
use std::sync::{Arc, Mutex};
use std::time::Duration;

use eukhe_tui::interactive::{
    run_interactive, HeadlessPlan, HeadlessStep, InteractiveOptions, ModelSelection,
    SessionSelection, UiMode,
};
use serde_json::{json, Value};

/// The prompt every test submits.
const PROMPT: &str = "say hi";
/// The answer a turn that answers streams.
const ANSWER: &str = "hello there";
/// The row a turn that ended with no reply leaves.
const NO_REPLY: &str = "The turn ended without a reply";
/// The next step of a failure or a turn with no reply.
const RESEND: &str = "Next: send the message again, or pick another model with /model.";
/// The client's own wait for a prompt ack (`UI_REQUEST_TIMEOUT_MS`) and a
/// margin: a lost ack surfaces after it.
const LOST_ACK_MS: u64 = 11_000;

/// The working indicator's phase labels (`TurnPhase::label`).
const LOADER_LABELS: [&str; 10] = [
    "Sending",
    "Queued",
    "Reconnecting",
    "Waiting",
    "Thinking",
    "Writing",
    "Writing code",
    "Executing",
    "Compacting",
    "Retrying",
];

/// What the stored session looks like at an attach.
#[derive(Clone)]
struct Snapshot {
    /// A run is open (`isStreaming`).
    streaming: bool,
    /// A compaction runs (`isCompacting`).
    compacting: bool,
    /// The stored messages.
    messages: Vec<Value>,
    /// The prompt the session is preparing a turn for, if any.
    preparing: Option<&'static str>,
}

impl Snapshot {
    fn idle(messages: Vec<Value>) -> Self {
        Snapshot {
            streaming: false,
            compacting: false,
            messages,
            preparing: None,
        }
    }
}

/// One step of the mock daemon, in order.
enum Act {
    /// Wait for the client's prompt request.
    Prompt,
    /// Answer the prompt: admitted.
    Admit,
    /// Answer the prompt: refused with this error.
    Refuse(&'static str),
    /// One session event.
    Event(Value),
    /// The session closes for this reason.
    Closed(&'static str),
    /// The worker is replaced: the client re-attaches to the session under
    /// a new id and rebuilds its chat from this snapshot.
    Rebuild(Snapshot),
    /// Hold the script.
    Hold(u64),
}

/// The mock daemon's state the request loop and the script share.
struct Shared {
    writer: Mutex<UnixStream>,
    current: Mutex<String>,
    snapshot: Mutex<Snapshot>,
}

impl Shared {
    fn write(&self, value: &Value) {
        let mut line = serde_json::to_string(value).expect("serialize mock frame");
        line.push('\n');
        let mut writer = self.writer.lock().expect("mock writer");
        let _ = writer.write_all(line.as_bytes());
        let _ = writer.flush();
    }

    fn current(&self) -> String {
        self.current.lock().expect("mock id").clone()
    }
}

fn response(id: &str, command: &str, data: &Value) -> Value {
    json!({ "type": "response", "id": id, "command": command, "success": true, "data": data })
}

fn attach_response(id: &str, active_session_id: &str, snapshot: &Snapshot) -> Value {
    let mut actions = json!({ "queuedCount": 0, "steering": [], "followUps": [] });
    if let Some(label) = snapshot.preparing {
        actions["active"] = json!({ "kind": "turn", "phase": "preparing", "label": label });
    }
    response(
        id,
        "attach",
        &json!({
            "protocol": { "name": "eukhe.daemon", "version": 7 },
            "activeSessionId": active_session_id,
            "snapshot": {
                "activeSessionId": active_session_id,
                "summary": { "id": active_session_id, "cwd": "/tmp" },
                "state": {
                    "activeSessionId": active_session_id,
                    "cwd": "/tmp",
                    "sessionId": "sess-1",
                    "sessionName": "turn visibility",
                    "model": null,
                    "isStreaming": snapshot.streaming,
                    "isCompacting": snapshot.compacting,
                    "sessionActions": actions,
                },
                "messages": snapshot.messages,
                "lastEventSequence": 0,
                "lastEventCursor": null,
            },
            "client": { "id": "mock", "capabilities": [] },
            "lastEventSequence": 0,
            "lastEventCursor": null,
        }),
    )
}

/// Answer the client's requests until it disconnects: the attach from the
/// current snapshot, the prompt handed to the script, everything else an
/// empty success.
fn serve_requests(
    stream: UnixStream,
    shared: &Shared,
    prompts: &mpsc::Sender<String>,
    attaches: &mpsc::Sender<String>,
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
        let id = envelope.get("id").and_then(Value::as_str).unwrap_or("");
        let command = envelope.get("command").cloned().unwrap_or(Value::Null);
        let command_type = command
            .get("type")
            .and_then(Value::as_str)
            .unwrap_or_default()
            .to_string();
        match command_type.as_str() {
            "create" => shared.write(&response(
                id,
                "create",
                &json!({
                    "activeSessionId": "s1",
                    "id": "s1",
                    "sessionId": "sess-1",
                    "sessionFile": "/tmp/sess-1.jsonl",
                }),
            )),
            "attach" => {
                let target = command
                    .get("activeSessionId")
                    .and_then(Value::as_str)
                    .unwrap_or("s1")
                    .to_string();
                let snapshot = shared.snapshot.lock().expect("mock snapshot").clone();
                shared.write(&attach_response(id, &target, &snapshot));
                let _ = attaches.send(target);
            }
            "prompt" => {
                let _ = prompts.send(id.to_string());
            }
            _ => shared.write(&response(id, &command_type, &json!({}))),
        }
    }
}

/// Serve one client: greet it, answer its requests, and play `script`.
fn serve(listener: &UnixListener, initial: Snapshot, script: Vec<Act>) {
    listener
        .set_nonblocking(true)
        .expect("nonblocking mock listener");
    let idle_until = std::time::Instant::now() + Duration::from_secs(5);
    let stream = loop {
        match listener.accept() {
            Ok((stream, _)) => break stream,
            Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                assert!(
                    std::time::Instant::now() < idle_until,
                    "the client never connected"
                );
                std::thread::sleep(Duration::from_millis(10));
            }
            Err(error) => panic!("mock accept: {error}"),
        }
    };
    stream.set_nonblocking(false).expect("blocking mock stream");
    let shared = Arc::new(Shared {
        writer: Mutex::new(stream.try_clone().expect("clone mock socket")),
        current: Mutex::new("s1".to_string()),
        snapshot: Mutex::new(initial),
    });
    shared.write(&json!({
        "type": "daemon_hello",
        "protocol": { "name": "eukhe.daemon", "version": 7 },
        "serverCapabilities": [],
        "clientId": "mock",
    }));
    let (prompt_tx, prompt_rx) = mpsc::channel();
    let (attach_tx, attach_rx) = mpsc::channel();
    let requests = {
        let shared = Arc::clone(&shared);
        std::thread::spawn(move || serve_requests(stream, &shared, &prompt_tx, &attach_tx))
    };
    let mut prompt_id = String::new();
    let mut workers = 1;
    for act in script {
        match act {
            Act::Prompt => {
                prompt_id = prompt_rx
                    .recv_timeout(Duration::from_secs(10))
                    .expect("the client sends its prompt");
            }
            Act::Admit => shared.write(&response(&prompt_id, "prompt", &json!({}))),
            Act::Refuse(error) => shared.write(&json!({
                "type": "response",
                "id": prompt_id,
                "command": "prompt",
                "success": false,
                "error": error,
            })),
            Act::Event(event) => shared.write(&json!({
                "type": "session_event",
                "activeSessionId": shared.current(),
                "event": event,
            })),
            Act::Closed(reason) => shared.write(&json!({
                "type": "session_closed",
                "activeSessionId": shared.current(),
                "reason": reason,
            })),
            Act::Rebuild(snapshot) => {
                workers += 1;
                let replacement = format!("s{workers}");
                *shared.snapshot.lock().expect("mock snapshot") = snapshot;
                shared.write(&json!({
                    "type": "session_binding",
                    "previousActiveSessionId": shared.current(),
                    "activeSessionId": replacement,
                }));
                loop {
                    let attached = attach_rx
                        .recv_timeout(Duration::from_secs(10))
                        .expect("the client re-attaches to the replacement");
                    if attached == replacement {
                        break;
                    }
                }
                *shared.current.lock().expect("mock id") = replacement;
            }
            Act::Hold(ms) => std::thread::sleep(Duration::from_millis(ms)),
        }
    }
    requests.join().expect("mock request loop");
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
fn run(initial: Snapshot, script: Vec<Act>, steps: Vec<HeadlessStep>) -> Vec<String> {
    // The ambient TMUX variable adds a startup notice to the transcript.
    std::env::remove_var("TMUX");
    let dir = tempfile::TempDir::new().expect("temp dir");
    let socket = dir.path().join("tui.sock");
    let listener = UnixListener::bind(&socket).expect("bind mock socket");
    let daemon = std::thread::spawn(move || serve(&listener, initial, script));
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
    daemon.join().expect("mock daemon finished");
    outcome.frames
}

fn wait_for(needle: &str) -> HeadlessStep {
    HeadlessStep::WaitRender {
        needle: needle.to_string(),
        timeout_ms: 5_000,
    }
}

/// The working indicator a frame shows: its phase label and the first
/// token of its elapsed time ("Waiting - 3s", "Waiting - 2h").
fn loader(frame: &str) -> Option<String> {
    frame.lines().find_map(|line| {
        LOADER_LABELS.iter().find_map(|label| {
            let marker = format!("{label} - ");
            let at = line.find(&marker)?;
            let elapsed = line[at + marker.len()..].split_whitespace().next()?;
            elapsed
                .starts_with(|c: char| c.is_ascii_digit())
                .then(|| format!("{marker}{elapsed}"))
        })
    })
}

fn all_frames(frames: &[String]) -> String {
    frames.join("\n=====\n")
}

/// A frame's text with every run of whitespace one space: a row the
/// terminal width wrapped reads whole again.
fn flat(frame: &str) -> String {
    frame.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// The final frame: no indicator, and exactly one row saying the turn
/// ended without an answer (`row`), which names `next`.
fn assert_ended_with_one_row(frames: &[String], row: &str, next: &str) {
    let last = frames.last().expect("a final frame");
    assert_eq!(
        loader(last),
        None,
        "no indicator once nothing runs:\n{last}"
    );
    let text = flat(last);
    assert_eq!(text.matches(row).count(), 1, "exactly one end row:\n{last}");
    assert!(text.contains(next), "the row names the next step:\n{last}");
}

/// Every frame from the Enter's loader until the first frame showing
/// `until` shows the indicator: the turn never runs without it.
fn assert_loader_until(frames: &[String], until: &str) {
    let first = frames
        .iter()
        .position(|frame| loader(frame).is_some())
        .unwrap_or_else(|| panic!("an indicator after Enter:\n{}", all_frames(frames)));
    let end = frames
        .iter()
        .position(|frame| frame.contains(until))
        .unwrap_or_else(|| panic!("a frame shows {until:?}:\n{}", all_frames(frames)));
    for frame in &frames[first..end] {
        assert!(
            loader(frame).is_some(),
            "the indicator dropped while the turn ran:\n{frame}"
        );
    }
}

fn user(text: &str, timestamp: u64) -> Value {
    json!({ "role": "user", "content": [{ "type": "text", "text": text }], "timestamp": timestamp })
}

fn assistant(content: Value, stop_reason: &str, error: Option<&str>) -> Value {
    let mut message = json!({
        "role": "assistant",
        "content": [],
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
    message["content"] = content;
    if let Some(error) = error {
        message["errorMessage"] = json!(error);
    }
    message
}

fn text(text: &str) -> Value {
    json!([{ "type": "text", "text": text }])
}

fn answer_message() -> Value {
    assistant(text(ANSWER), "stop", None)
}

fn now_ms() -> u64 {
    u64::try_from(
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("clock after the epoch")
            .as_millis(),
    )
    .expect("ms fit u64")
}

fn ev(kind: &str) -> Act {
    Act::Event(json!({ "type": kind }))
}

fn run_start() -> Act {
    ev("agent_start")
}

fn run_end() -> Act {
    Act::Event(json!({ "type": "agent_end", "messages": [] }))
}

/// The user message's `message_start` and `message_end`.
fn user_message() -> Vec<Act> {
    let message = user(PROMPT, now_ms());
    vec![
        Act::Event(json!({ "type": "message_start", "message": message })),
        Act::Event(json!({ "type": "message_end", "message": message })),
    ]
}

/// An assistant message's `message_start` and `message_end`.
fn message(message: &Value) -> Vec<Act> {
    vec![
        Act::Event(json!({
            "type": "message_start",
            "message": message,
            "assistantMessageEvent": { "type": "start" },
        })),
        Act::Event(json!({ "type": "message_end", "message": message })),
    ]
}

fn turn_end(message: &Value) -> Act {
    Act::Event(json!({ "type": "turn_end", "message": message, "toolResults": [] }))
}

/// Admitted, then a turn that answers.
fn answering_turn() -> Vec<Act> {
    let mut acts = vec![run_start(), ev("turn_start")];
    acts.extend(user_message());
    acts.extend(message(&answer_message()));
    acts.push(turn_end(&answer_message()));
    acts.push(run_end());
    acts
}

/// F1: a rebuild while the prompt travels, and again once it is admitted
/// but its run has not started, keeps the indicator up.
#[test]
fn f1_a_rebuild_while_the_prompt_travels_or_waits_keeps_the_indicator() {
    let mut script = vec![
        Act::Prompt,
        Act::Hold(300),
        Act::Rebuild(Snapshot::idle(Vec::new())),
        Act::Hold(300),
        Act::Admit,
        Act::Hold(300),
        Act::Rebuild(Snapshot {
            preparing: Some(PROMPT),
            ..Snapshot::idle(Vec::new())
        }),
        Act::Hold(300),
        Act::Event(json!({
            "type": "session_action_update",
            "actions": { "queuedCount": 0, "steering": [], "followUps": [] },
        })),
    ];
    script.extend(answering_turn());
    let frames = run(
        Snapshot::idle(Vec::new()),
        script,
        vec![wait_for(ANSWER), HeadlessStep::WaitMs(300)],
    );
    assert_loader_until(&frames, ANSWER);
    assert_eq!(loader(frames.last().expect("a frame")), None);
}

/// F2: the run ends before its first request while the ack travels; the
/// late ack re-arms nothing, and the turn says it ended without a reply.
#[test]
fn f2_a_run_that_ends_before_the_ack_leaves_its_row_and_no_indicator() {
    let frames = run(
        Snapshot::idle(Vec::new()),
        vec![
            Act::Prompt,
            run_start(),
            run_end(),
            Act::Hold(300),
            Act::Admit,
        ],
        vec![wait_for(NO_REPLY), HeadlessStep::WaitMs(800)],
    );
    assert_ended_with_one_row(&frames, NO_REPLY, RESEND);
}

/// F3: an ack after the session closed re-arms no indicator.
#[test]
fn f3_an_ack_after_the_session_closed_raises_no_indicator() {
    let frames = run(
        Snapshot::idle(Vec::new()),
        vec![
            Act::Prompt,
            Act::Closed("killed"),
            Act::Hold(300),
            Act::Admit,
        ],
        vec![
            wait_for("The daemon stopped this agent session"),
            HeadlessStep::WaitMs(800),
        ],
    );
    assert_ended_with_one_row(
        &frames,
        "The daemon stopped this agent session",
        "reopened from Agents View",
    );
}

/// F4: an admitted run that ends before its first request says the turn
/// ended without a reply.
#[test]
fn f4_a_run_that_ends_before_any_request_says_so() {
    let frames = run(
        Snapshot::idle(Vec::new()),
        vec![Act::Prompt, Act::Admit, run_start(), run_end()],
        vec![wait_for(NO_REPLY), HeadlessStep::WaitMs(300)],
    );
    assert_ended_with_one_row(&frames, NO_REPLY, RESEND);
}

/// F4: a run that ends after a tool round with no answering turn (an abort
/// during the tools) says the turn ended without a reply.
#[test]
fn f4_a_run_that_ends_after_a_tool_round_says_so() {
    let tools = assistant(
        json!([
            { "type": "text", "text": "listing" },
            { "type": "toolCall", "id": "c1", "name": "bash", "arguments": { "command": "ls" } },
        ]),
        "toolUse",
        None,
    );
    let mut script = vec![Act::Prompt, Act::Admit, run_start(), ev("turn_start")];
    script.extend(user_message());
    script.extend(message(&tools));
    script.push(turn_end(&tools));
    script.push(run_end());
    let frames = run(
        Snapshot::idle(Vec::new()),
        script,
        vec![wait_for(NO_REPLY), HeadlessStep::WaitMs(300)],
    );
    assert_ended_with_one_row(&frames, NO_REPLY, RESEND);
}

/// F5: a `turn_end` with neither an answer nor an error says the turn
/// ended without a reply.
#[test]
fn f5_an_unreported_turn_end_says_so() {
    let mut script = vec![Act::Prompt, Act::Admit, run_start(), ev("turn_start")];
    script.extend(user_message());
    script.push(ev("turn_end"));
    script.push(run_end());
    let frames = run(
        Snapshot::idle(Vec::new()),
        script,
        vec![wait_for(NO_REPLY), HeadlessStep::WaitMs(300)],
    );
    assert_ended_with_one_row(&frames, NO_REPLY, RESEND);
}

/// F6: a rebuild after a refused prompt keeps the refusal row.
#[test]
fn f6_a_rebuild_keeps_the_refused_prompt_row() {
    let elsewhere = vec![
        user("from another window", 1),
        assistant(text("the other answer"), "stop", None),
    ];
    let frames = run(
        Snapshot::idle(Vec::new()),
        vec![
            Act::Prompt,
            Act::Refuse("Queue is full"),
            Act::Hold(300),
            Act::Rebuild(Snapshot::idle(elsewhere)),
        ],
        vec![
            wait_for("Queue is full"),
            wait_for("the other answer"),
            HeadlessStep::WaitMs(300),
        ],
    );
    assert_ended_with_one_row(
        &frames,
        "Queue is full",
        "Next: the message is back in the editor",
    );
}

/// F7: a refused prompt's row names the next step.
#[test]
fn f7_a_refused_prompt_names_the_next_step() {
    let frames = run(
        Snapshot::idle(Vec::new()),
        vec![Act::Prompt, Act::Refuse("Queue is full")],
        vec![wait_for("Queue is full"), HeadlessStep::WaitMs(300)],
    );
    assert_ended_with_one_row(
        &frames,
        "Queue is full",
        "Next: the message is back in the editor; send it again",
    );
}

/// F7: a prompt whose ack never comes names the next step.
#[test]
fn f7_a_lost_ack_names_the_next_step() {
    let frames = run(
        Snapshot::idle(Vec::new()),
        vec![Act::Prompt, Act::Hold(LOST_ACK_MS)],
        vec![
            HeadlessStep::WaitRender {
                needle: "may still be in flight".to_string(),
                timeout_ms: LOST_ACK_MS + 4_000,
            },
            HeadlessStep::WaitMs(300),
        ],
    );
    assert_ended_with_one_row(
        &frames,
        "may still be in flight",
        "Next: wait for the turn to show here; if it does not, send the message again.",
    );
}

/// F8: the "Primary provider recovered" notice of a failover that
/// recovered passes as a toast: the stored transcript has no record of
/// it, so the chat keeps no row a reopened chat would lack.
#[test]
fn f8_a_recovered_failover_leaves_no_live_only_row() {
    let failed = assistant(json!([]), "error", Some("429 rate_limit_error"));
    let mut script = vec![Act::Prompt, Act::Admit, run_start(), ev("turn_start")];
    script.extend(user_message());
    script.extend(message(&failed));
    script.push(Act::Event(json!({
        "type": "auto_retry_start",
        "attempt": 1,
        "maxAttempts": 8,
        "delayMs": 0,
        "errorMessage": "429 rate_limit_error",
        "reason": "backup",
        "backupModel": "backup/faux-2",
    })));
    script.extend(message(&answer_message()));
    script.push(Act::Event(json!({
        "type": "auto_retry_end",
        "success": true,
        "attempt": 1,
        "restoredModel": "faux/faux-1",
    })));
    script.push(turn_end(&answer_message()));
    script.push(run_end());
    let frames = run(
        Snapshot::idle(Vec::new()),
        script,
        // Past the toast's life (`TOAST_TTL`, 3s).
        vec![wait_for(ANSWER), HeadlessStep::WaitMs(3_500)],
    );
    assert!(
        frames
            .iter()
            .any(|frame| frame.contains("Primary provider recovered")),
        "the recovery shows:\n{}",
        all_frames(&frames)
    );
    let last = frames.last().expect("a final frame");
    assert!(last.contains(ANSWER), "the answer shows:\n{last}");
    assert!(
        !last.contains("Primary provider recovered") && !last.contains("429"),
        "the recovered turn leaves no live-only row:\n{last}"
    );
    assert_eq!(loader(last), None, "no indicator:\n{last}");
}

/// F9: a re-attach before the turn's prompt is stored keeps the clock of
/// the Enter, not the previous turn's prompt two hours ago.
#[test]
fn f9_a_rebuild_before_the_prompt_is_stored_keeps_the_clock_of_the_enter() {
    let earlier = vec![
        user("an earlier question", now_ms() - 2 * 60 * 60 * 1000),
        assistant(text("an earlier answer"), "stop", None),
    ];
    let mut script = vec![
        Act::Prompt,
        Act::Admit,
        run_start(),
        ev("turn_start"),
        Act::Hold(300),
        Act::Rebuild(Snapshot {
            streaming: true,
            ..Snapshot::idle(earlier.clone())
        }),
        Act::Hold(800),
    ];
    script.extend(user_message());
    script.extend(message(&answer_message()));
    script.push(turn_end(&answer_message()));
    script.push(run_end());
    let frames = run(
        Snapshot::idle(earlier),
        script,
        vec![wait_for(ANSWER), HeadlessStep::WaitMs(300)],
    );
    assert_loader_until(&frames, ANSWER);
    for indicator in frames.iter().filter_map(|frame| loader(frame)) {
        assert!(
            indicator.ends_with('s'),
            "the clock counts from the Enter: {indicator}"
        );
    }
}

/// F10: the lost ack's row retires once the turn shows after all: the
/// answer is the turn's only ending.
#[test]
fn f10_a_lost_ack_row_retires_when_the_turn_shows() {
    let mut script = vec![Act::Prompt, Act::Hold(LOST_ACK_MS)];
    script.extend(answering_turn());
    let frames = run(
        Snapshot::idle(Vec::new()),
        script,
        vec![
            HeadlessStep::WaitRender {
                needle: "may still be in flight".to_string(),
                timeout_ms: LOST_ACK_MS + 4_000,
            },
            wait_for(ANSWER),
            HeadlessStep::WaitMs(300),
        ],
    );
    let last = frames.last().expect("a final frame");
    assert!(last.contains(ANSWER), "the answer shows:\n{last}");
    assert!(
        !last.contains("may still be in flight") && !last.contains("Error:"),
        "no row says the answered turn failed:\n{last}"
    );
    assert_eq!(loader(last), None, "no indicator:\n{last}");
}

/// F11: a rebuild between the answer's `turn_end` and the run's
/// `agent_end` raises no indicator after the answer.
#[test]
fn f11_a_rebuild_after_the_answer_raises_no_indicator() {
    let mut script = vec![Act::Prompt, Act::Admit, run_start(), ev("turn_start")];
    let stored_user = user(PROMPT, now_ms());
    script.extend(user_message());
    script.extend(message(&answer_message()));
    script.push(turn_end(&answer_message()));
    script.push(Act::Hold(300));
    script.push(Act::Rebuild(Snapshot {
        streaming: true,
        ..Snapshot::idle(vec![stored_user, answer_message()])
    }));
    script.push(Act::Hold(1_000));
    script.push(run_end());
    let frames = run(
        Snapshot::idle(Vec::new()),
        script,
        vec![wait_for(ANSWER), HeadlessStep::WaitMs(2_000)],
    );
    let answered = frames
        .iter()
        .position(|frame| frame.contains(ANSWER) && loader(frame).is_none())
        .unwrap_or_else(|| panic!("the answer settles:\n{}", all_frames(&frames)));
    for frame in &frames[answered..] {
        assert_eq!(
            loader(frame),
            None,
            "no indicator after the answer:\n{frame}"
        );
    }
}

/// F12: a rebuild during a compaction outside any turn shows it, and its
/// `compaction_end` takes the indicator down.
#[test]
fn f12_a_rebuilt_compaction_outside_a_turn_ends_with_no_indicator() {
    let frames = run(
        Snapshot::idle(Vec::new()),
        vec![
            Act::Prompt,
            Act::Refuse("Queue is full"),
            Act::Event(json!({ "type": "compaction_start", "reason": "threshold" })),
            Act::Hold(300),
            Act::Rebuild(Snapshot {
                compacting: true,
                ..Snapshot::idle(Vec::new())
            }),
            Act::Hold(500),
            Act::Event(json!({
                "type": "compaction_end",
                "reason": "threshold",
                "aborted": false,
                "willRetry": false,
            })),
        ],
        vec![
            wait_for("Queue is full"),
            wait_for("Compacting - "),
            HeadlessStep::WaitGone {
                needle: "Compacting - ".to_string(),
                timeout_ms: 5_000,
            },
            HeadlessStep::WaitMs(300),
        ],
    );
    assert_eq!(loader(frames.last().expect("a frame")), None);
}

/// F13: a `completed` closure mid-turn leaves an error row naming how to
/// go on, not a passing note.
#[test]
fn f13_a_completed_closure_mid_turn_says_so() {
    let mut script = vec![Act::Prompt, Act::Admit, run_start(), ev("turn_start")];
    script.extend(user_message());
    script.push(Act::Closed("completed"));
    let frames = run(
        Snapshot::idle(Vec::new()),
        script,
        vec![
            wait_for("while a turn was running"),
            HeadlessStep::WaitMs(300),
        ],
    );
    assert_ended_with_one_row(
        &frames,
        "Error: The session closed (completed) while a turn was running.",
        "reopen it from Agents View",
    );
}

/// F15: a reply that streamed text and then failed, with the failure
/// disclosed by its outcome row, shows the failure once.
#[test]
fn f15_a_failed_reply_with_its_outcome_row_shows_the_error_once() {
    let failed = assistant(text("Here is the pl"), "error", Some("529 overloaded"));
    let outcome = json!({
        "role": "custom",
        "customType": "provider_retry_outcome",
        "content": "Retry failed after 0 attempts: 529 overloaded",
        "display": true,
        "details": { "success": false, "attempts": 0, "finalError": "529 overloaded" },
        "timestamp": 2,
    });
    let mut script = vec![Act::Prompt, Act::Admit, run_start(), ev("turn_start")];
    script.extend(user_message());
    script.extend(message(&failed));
    script.push(turn_end(&failed));
    script.push(Act::Event(
        json!({ "type": "message_start", "message": outcome }),
    ));
    script.push(Act::Event(
        json!({ "type": "message_end", "message": outcome }),
    ));
    script.push(run_end());
    let frames = run(
        Snapshot::idle(Vec::new()),
        script,
        vec![
            wait_for("Retry failed after 0 attempts"),
            HeadlessStep::WaitMs(300),
        ],
    );
    let last = frames.last().expect("a final frame");
    assert!(
        last.contains("Here is the pl"),
        "the reply keeps its text:\n{last}"
    );
    assert_ended_with_one_row(&frames, "529 overloaded", RESEND);
}

/// F16: a closure during a retry wait keeps the failed attempt's row, as
/// the stored transcript does.
#[test]
fn f16_a_closure_in_a_retry_wait_keeps_the_failed_attempt() {
    let failed = assistant(json!([]), "error", Some("529 overloaded"));
    let mut script = vec![Act::Prompt, Act::Admit, run_start(), ev("turn_start")];
    script.extend(user_message());
    script.extend(message(&failed));
    script.push(Act::Event(json!({
        "type": "auto_retry_start",
        "attempt": 1,
        "maxAttempts": 3,
        "delayMs": 30_000,
        "errorMessage": "529 overloaded",
    })));
    script.push(Act::Hold(300));
    script.push(Act::Closed("killed"));
    let frames = run(
        Snapshot::idle(Vec::new()),
        script,
        vec![
            wait_for("The daemon stopped this agent session"),
            HeadlessStep::WaitMs(300),
        ],
    );
    assert_ended_with_one_row(&frames, "Error: 529 overloaded", RESEND);
}
