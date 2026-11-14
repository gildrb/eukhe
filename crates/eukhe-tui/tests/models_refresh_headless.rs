//! Headless e2e for `/models refresh` in the inline client: the command
//! sends `refresh_models` and shows the answer's report lines; a refused
//! refresh is the error row.
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

fn write_json(writer: &mut UnixStream, value: &Value) {
    let mut line = serde_json::to_string(value).expect("serialize mock frame");
    line.push('\n');
    writer.write_all(line.as_bytes()).expect("write mock frame");
    writer.flush().expect("flush mock frame");
}

/// The mock supervisor: the hello, `attach`, the scripted answer to
/// `refresh_models`, and an empty success for everything else. Returns the
/// `refresh_models` commands it received.
fn serve(listener: &UnixListener, refresh: &Result<Value, &str>) -> Vec<Value> {
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
        let answer: Result<Value, &str> = match command_type {
            "attach" => Ok(attach_data()),
            "refresh_models" => {
                received.push(command.clone());
                refresh.clone()
            }
            _ => Ok(json!({})),
        };
        let mut response = json!({
            "type": "response",
            "id": id,
            "command": command_type,
            "success": answer.is_ok(),
        });
        match answer {
            Ok(data) => response["data"] = data,
            Err(error) => response["error"] = json!(error),
        }
        write_json(&mut writer, &response);
    }
    received
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
            "messages": [],
            "lastEventSequence": 0,
            "lastEventCursor": null,
        },
        "client": { "id": "mock", "capabilities": [] },
        "lastEventSequence": 0,
        "lastEventCursor": null,
    })
}

/// The answer of a refresh that added `prov/refreshed-1`.
fn refreshed_answer() -> Value {
    json!({
        "models": [{
            "id": "refreshed-1",
            "name": "Refreshed One",
            "api": "openai-responses",
            "provider": "prov",
            "baseUrl": "https://prov.test/v1",
            "reasoning": false,
            "input": ["text"],
            "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
            "contextWindow": 128_000,
            "maxTokens": 8_192,
            "thinkingLevels": [],
            "serviceTiers": [],
        }],
        "configuredProviders": ["prov"],
        "modelsJsonErrors": [],
        "report": {
            "refreshedAt": "2026-11-14T10:00:00.000Z",
            "providers": [{
                "provider": "prov",
                "status": "refreshed",
                "added": [{ "id": "refreshed-1", "name": "Refreshed One" }],
                "known": 2,
            }],
        },
        "lines": [
            "Model lists refreshed at 11:00",
            "prov: 1 new, 2 already known",
            "  prov/refreshed-1  Refreshed One",
        ],
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

/// Run `steps` against the mock; the captured frames and the
/// `refresh_models` commands the mock received.
fn run(
    refresh: Result<Value, &'static str>,
    steps: Vec<HeadlessStep>,
) -> (Vec<String>, Vec<Value>) {
    std::env::remove_var("TMUX");
    let dir = tempfile::TempDir::new().expect("temp dir");
    let socket = dir.path().join("tui.sock");
    let listener = UnixListener::bind(&socket).expect("bind mock socket");
    let handle = std::thread::spawn(move || serve(&listener, &refresh));
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

/// `/models refresh` sends `refresh_models` and shows the report lines.
#[test]
fn the_refresh_shows_its_report() {
    let (frames, received) = run(
        Ok(refreshed_answer()),
        vec![
            wait("[M] faux-1"),
            submit("/models refresh"),
            wait("Refreshing model lists..."),
            wait("prov: 1 new, 2 already known"),
            wait("prov/refreshed-1  Refreshed One"),
            HeadlessStep::WaitIdle { timeout_ms: 10_000 },
        ],
    );
    let all = frames.join("\n---frame---\n");
    assert_eq!(
        received,
        vec![json!({ "type": "refresh_models", "activeSessionId": "s1" })],
        "frames:\n{all}"
    );
}

/// A refused refresh is the error row.
#[test]
fn a_refused_refresh_is_the_error_row() {
    let (frames, received) = run(
        Err("the overlay does not write"),
        vec![
            wait("[M] faux-1"),
            submit("/models refresh"),
            wait("the overlay does not write"),
            HeadlessStep::WaitIdle { timeout_ms: 10_000 },
        ],
    );
    let all = frames.join("\n---frame---\n");
    assert_eq!(received.len(), 1, "frames:\n{all}");
}
