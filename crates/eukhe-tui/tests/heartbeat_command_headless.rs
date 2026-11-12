//! Headless e2e for the advertised `/heartbeat` command (TS
//! `handleHeartbeatCommand`): the client parses it and drives the session's
//! own heartbeat over `heartbeat_get` / `heartbeat_set` /
//! `heartbeat_update`, answering with the TS status rows -- never the
//! `is not available in this client yet` note.
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

const NEXT_RUN: &str = "2026-11-09T12:01:00.000Z";

fn write_json(writer: &mut UnixStream, value: &Value) {
    let mut line = serde_json::to_string(value).expect("serialize mock frame");
    line.push('\n');
    writer.write_all(line.as_bytes()).expect("write mock frame");
    writer.flush().expect("flush mock frame");
}

/// The daemon's heartbeat job for a `heartbeat_set` (the worker's
/// `create_heartbeat`: the default delivery is steer).
fn heartbeat_job(command: &Value) -> Value {
    json!({
        "id": "hb-1",
        "status": "active",
        "source": "heartbeat",
        "deliveryMode": command.get("deliveryMode").cloned().unwrap_or(json!("steer")),
        "activeSessionId": "s1",
        "sessionId": "sess-1",
        "sessionFile": "/tmp/sess-1.jsonl",
        "cwd": "/tmp",
        "prompt": command["prompt"],
        "schedule": { "kind": "interval", "expression": command["schedule"], "intervalMs": 60_000 },
        "createdAt": "2026-11-09T12:00:00.000Z",
        "updatedAt": "2026-11-09T12:00:00.000Z",
        "nextRunAt": NEXT_RUN,
        "runCount": 0,
    })
}

/// The mock supervisor: the hello, `attach`, and a one-heartbeat store
/// behind `heartbeat_get` / `heartbeat_set` / `heartbeat_update`; an
/// empty success for everything else. Returns every command it got.
fn serve(listener: &UnixListener) -> Vec<Value> {
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
    let mut commands = Vec::new();
    let mut heartbeat = Value::Null;
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
        let command = envelope["command"].clone();
        let command_type = command["type"].as_str().unwrap_or_default().to_string();
        let data = match command_type.as_str() {
            "attach" => attach_data(),
            "heartbeat_get" => json!({ "heartbeat": heartbeat }),
            "heartbeat_set" => {
                heartbeat = heartbeat_job(&command);
                json!({ "heartbeat": heartbeat })
            }
            "heartbeat_update" => {
                let updated = match command["action"].as_str() {
                    _ if heartbeat.is_null() => Value::Null,
                    Some("pause") => {
                        heartbeat["status"] = json!("paused");
                        heartbeat.clone()
                    }
                    Some("resume") => {
                        heartbeat["status"] = json!("active");
                        heartbeat.clone()
                    }
                    _ => {
                        let mut cancelled = std::mem::take(&mut heartbeat);
                        cancelled["status"] = json!("cancelled");
                        cancelled
                    }
                };
                json!({ "heartbeat": updated })
            }
            "heartbeats_list" => json!({ "heartbeats": [] }),
            _ => json!({}),
        };
        commands.push(command);
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
    }
    commands
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
                    "api": "faux",
                    "provider": "faux",
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

/// `/heartbeat every 1m say hi` sets the session's heartbeat through
/// `heartbeat_set`; bare `/heartbeat` shows it; pause, resume and stop go
/// through `heartbeat_update`; a missing instruction is the TS usage
/// error, sent nowhere.
#[test]
fn the_heartbeat_command_drives_the_session_heartbeat() {
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
    let submit = |text: &str| HeadlessStep::Submit(text.to_string());
    let expected = [
        ("/heartbeat", "No active heartbeat"),
        ("/heartbeat every 1m say hi", "Heartbeat set"),
        ("/heartbeat", "Instruction: say hi"),
        ("/heartbeat pause", "Heartbeat paused"),
        ("/heartbeat resume", "Heartbeat resumed"),
        ("/heartbeat stop", "Heartbeat cleared"),
        (
            "/heartbeat every 2m --follow-up check in",
            "Delivery: follow_up",
        ),
        ("/heartbeat every 1m", "Usage: /heartbeat"),
    ];
    let mut steps = vec![wait("settled answer")];
    for (command, needle) in expected {
        steps.push(submit(command));
        steps.push(wait(needle));
    }
    steps.push(HeadlessStep::WaitIdle { timeout_ms: 10_000 });
    let plan = HeadlessPlan {
        steps,
        width: 120,
        height: 40,
    };
    let frames = runtime
        .block_on(run_interactive(options(socket), UiMode::Headless(plan)))
        .expect("interactive run")
        .frames;
    let commands = handle.join().expect("mock supervisor finished");
    let all = frames.join("\n---frame---\n");
    assert!(
        !all.contains("is not available in this client yet"),
        "/heartbeat is implemented:\n{all}"
    );
    for (command, needle) in expected {
        assert!(all.contains(needle), "{command:?} shows {needle:?}:\n{all}");
    }
    let heartbeat_commands: Vec<Value> = commands
        .into_iter()
        .filter(|command| {
            matches!(
                command["type"].as_str(),
                Some("heartbeat_get" | "heartbeat_set" | "heartbeat_update")
            )
        })
        .collect();
    assert_eq!(
        heartbeat_commands,
        vec![
            json!({ "type": "heartbeat_get", "activeSessionId": "s1" }),
            json!({
                "type": "heartbeat_set", "activeSessionId": "s1",
                "schedule": "every 1m", "prompt": "say hi",
            }),
            json!({ "type": "heartbeat_get", "activeSessionId": "s1" }),
            json!({ "type": "heartbeat_update", "activeSessionId": "s1", "action": "pause" }),
            json!({ "type": "heartbeat_update", "activeSessionId": "s1", "action": "resume" }),
            json!({ "type": "heartbeat_update", "activeSessionId": "s1", "action": "clear" }),
            json!({
                "type": "heartbeat_set", "activeSessionId": "s1",
                "schedule": "every 2m", "prompt": "check in", "deliveryMode": "follow_up",
            }),
        ],
        "the daemon requests, in order (the usage error sends nothing)"
    );
}
