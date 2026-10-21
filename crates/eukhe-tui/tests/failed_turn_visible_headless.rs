//! Headless e2e for a turn that ends without an answer (the 2026-10-21
//! incident): a provider failover re-routed the turn to a provider with no
//! key, the run failed in half a second, and the chat showed NOTHING -- the
//! retry give-up (`auto_retry_end` with a final error) popped the failed
//! attempt's error row, expecting a `provider_retry_outcome` row that never
//! came (the core discloses no row for a pre-request failure), and the
//! `turn_end` backstop stayed silent because the give-up had marked the
//! error as shown.
//!
//! The run replays the incident's exact wire sequence and checks the two
//! guarantees: a working indicator is on screen from the Enter on (before
//! the daemon answered anything), and the turn's end leaves exactly one
//! visible error row naming the error and the next step, with no loader.

use std::io::{BufRead, BufReader, Write};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::PathBuf;

use eukhe_tui::interactive::{
    run_interactive, HeadlessPlan, HeadlessStep, InteractiveOptions, ModelSelection,
    SessionSelection, UiMode,
};
use serde_json::{json, Value};

/// How long the mock holds the prompt before the daemon side answers: the
/// window the indicator must cover on its own.
const ADMISSION_DELAY_MS: u64 = 600;

const ERROR: &str = "No API key for provider: cloudflare-ai-gateway";

struct MockSupervisor {
    listener: UnixListener,
}

impl MockSupervisor {
    fn bind(socket: &std::path::Path) -> Self {
        MockSupervisor {
            listener: UnixListener::bind(socket).expect("bind mock socket"),
        }
    }

    /// Serve one client connection until it closes (bounded accept, so the
    /// plan teardown join always finishes).
    fn serve(self) {
        self.listener
            .set_nonblocking(true)
            .expect("nonblocking mock listener");
        let idle_until = std::time::Instant::now() + std::time::Duration::from_millis(3000);
        let (stream, _) = loop {
            match self.listener.accept() {
                Ok(accepted) => break accepted,
                Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                    if std::time::Instant::now() >= idle_until {
                        return;
                    }
                    std::thread::sleep(std::time::Duration::from_millis(10));
                }
                Err(_) => return,
            }
        };
        stream.set_nonblocking(false).expect("blocking mock stream");
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
                "attach" => write_json(&mut writer, &attach_data(id)),
                "prompt" => {
                    // The daemon side stays silent for the admission window,
                    // then admits the prompt and streams the incident's turn.
                    let mut event_writer = writer.try_clone().expect("clone event socket");
                    let id = id.to_string();
                    std::thread::spawn(move || {
                        std::thread::sleep(std::time::Duration::from_millis(ADMISSION_DELAY_MS));
                        write_json(&mut event_writer, &response(&id, "prompt", &json!({})));
                        for event in incident_events() {
                            write_json(
                                &mut event_writer,
                                &json!({
                                    "type": "session_event",
                                    "activeSessionId": "s1",
                                    "event": event,
                                }),
                            );
                        }
                    });
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
    let _ = writer.write_all(line.as_bytes());
    let _ = writer.flush();
}

/// The failed attempt as the worker committed it: no content, the error.
fn failed_message() -> Value {
    json!({
        "role": "assistant",
        "content": [],
        "api": "anthropic-messages",
        "provider": "cloudflare-ai-gateway",
        "model": "claude-opus-5-5",
        "usage": {
            "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 0,
            "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
        },
        "stopReason": "error",
        "errorMessage": ERROR,
        "timestamp": 1_792_616_923_552_u64,
    })
}

/// The incident's wire sequence (captured from the 0.10.45 daemon): the
/// primary's 429 fails over to a provider without a key, the failed
/// attempt lands, the retry loop gives up, the turn and the run end.
fn incident_events() -> Vec<Value> {
    let user = json!({
        "role": "user",
        "content": [{ "type": "text", "text": "say hi" }],
        "timestamp": 1_792_616_923_008_u64,
    });
    vec![
        json!({ "type": "agent_start" }),
        json!({ "type": "turn_start" }),
        json!({ "type": "message_start", "message": user }),
        json!({ "type": "message_end", "message": user }),
        json!({
            "type": "auto_retry_start",
            "attempt": 1,
            "maxAttempts": 8,
            "delayMs": 0,
            "errorMessage": "429 rate_limit_error",
            "reason": "backup",
            "backupModel": "cloudflare-ai-gateway/claude-opus-5-5",
        }),
        json!({ "type": "message_start", "message": failed_message() }),
        json!({ "type": "message_end", "message": failed_message() }),
        json!({
            "type": "auto_retry_end",
            "success": false,
            "attempt": 2,
            "finalError": ERROR,
        }),
        json!({ "type": "turn_end", "message": failed_message(), "toolResults": [] }),
        json!({ "type": "agent_end", "messages": [user, failed_message()] }),
    ]
}

fn attach_data(id: &str) -> Value {
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
                    "sessionName": "failed turn session",
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

#[test]
fn a_failed_turn_shows_the_indicator_then_exactly_one_error_with_its_next_step() {
    // The ambient TMUX variable adds a startup notice to the transcript.
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
            HeadlessStep::Submit("say hi".to_string()),
            // Inside the admission window: nothing came back yet.
            HeadlessStep::WaitMs(ADMISSION_DELAY_MS / 2),
            HeadlessStep::WaitRender {
                needle: "Next: sign in".to_string(),
                timeout_ms: 5000,
            },
            HeadlessStep::WaitMs(200),
        ],
        width: 140,
        height: 40,
    };
    let outcome = runtime
        .block_on(run_interactive(options(socket), UiMode::Headless(plan)))
        .expect("interactive run");
    handle.join().expect("mock supervisor finished");

    let sending = outcome
        .frames
        .iter()
        .any(|frame| frame.contains("Sending - 0s"));
    assert!(
        sending,
        "the indicator is up right after Enter:\n{}",
        outcome.frames.join("\n=====\n")
    );

    // The end of the failed turn: one error row, its next step, no loader.
    let last = outcome.frames.last().expect("a final frame");
    assert_eq!(
        last.matches(ERROR).count(),
        1,
        "exactly one error row names the failure:\n{last}"
    );
    assert!(
        last.contains(
            "Next: sign in with /login, set the cloudflare-ai-gateway API key, or pick another model with /model."
        ),
        "the error row names the next step:\n{last}"
    );
    for loader in [
        "Sending - ",
        "Queued - ",
        "Waiting - ",
        "Retrying",
        "retrying on backup",
    ] {
        assert!(
            !last.contains(loader),
            "no working indicator after the turn ended ({loader}):\n{last}"
        );
    }
}
