//! Headless verifier for a session whose worker stays unreachable past the
//! session re-attach window (a disk that filled up kept the daemon from
//! reopening it): once the daemon can serve the session again, the next
//! submit re-attaches it and the prompt is answered. A mock supervisor
//! hands out a direct worker link; the mock worker closes it, the
//! supervisor refuses the re-attach the window allows, then serves the
//! session again. The window is the injected test window (0 ms), so the
//! test waits only on what the screen shows.

use std::io::{BufRead, BufReader, Read, Write};
use std::os::unix::net::UnixListener;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Duration;

use eukhe_tui::interactive::{
    run_interactive, HeadlessPlan, HeadlessStep, InteractiveOptions, ModelSelection,
    SessionSelection, UiMode,
};
use eukhe_types::daemon::framing::{
    encode_private_frame, PrivateFrameDecoder, DEFAULT_PRIVATE_FRAME_LIMITS,
};
use serde_json::{json, Value};

const PROMPT: &str = "after the disk came back";
const ANSWER: &str = "answered again";
/// The session re-attach window's test seam (`interactive/reconnect.rs`).
const RECONNECT_WINDOW_ENV: &str = "EUKHE_TEST_SESSION_RECONNECT_WINDOW_MS";

fn response(id: &str, command: &str, data: &Value) -> Value {
    json!({ "type": "response", "id": id, "command": command, "success": true, "data": data })
}

fn attach_data(active_session_id: &str) -> Value {
    json!({
        "protocol": { "name": "eukhe.daemon", "version": 7 },
        "activeSessionId": active_session_id,
        "snapshot": {
            "activeSessionId": active_session_id,
            "summary": { "id": active_session_id, "cwd": "/tmp" },
            "state": {
                "activeSessionId": active_session_id,
                "cwd": "/tmp",
                "sessionId": "sess-1",
                "sessionName": "reattach",
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

fn frame(header: &Value, payload: &Value) -> Vec<u8> {
    encode_private_frame(
        header,
        &serde_json::to_vec(payload).expect("serialize payload"),
        DEFAULT_PRIVATE_FRAME_LIMITS,
    )
    .expect("encode frame")
}

/// The session worker behind the direct link: hello, `peer_auth`, the
/// attach, then it dies (closes the link) and never comes back.
fn serve_worker(listener: &UnixListener, died: &AtomicBool) {
    let (mut stream, _) = listener.accept().expect("worker accept");
    stream
        .write_all(&frame(
            &json!({ "kind": "outbound", "outboundType": "daemon_hello" }),
            &json!({ "type": "daemon_hello", "protocol": { "name": "eukhe.daemon", "version": 7 } }),
        ))
        .expect("worker hello");
    let mut decoder = PrivateFrameDecoder::new(DEFAULT_PRIVATE_FRAME_LIMITS);
    let mut chunk = [0u8; 8192];
    let mut attached = false;
    while !attached {
        let read = stream.read(&mut chunk).expect("worker read");
        assert!(read > 0, "the client closed the direct link first");
        for command in decoder.push(&chunk[..read]).expect("decode frames") {
            let command_type = command.header["commandType"].as_str().unwrap_or_default();
            let request_id = command.header["requestId"].as_str().unwrap_or_default();
            let (success, data) = match command_type {
                "peer_auth" => (
                    true,
                    json!({
                        "workerInstanceId": "inst-1",
                        "activeSessionId": "s1",
                        "purpose": "session_client",
                    }),
                ),
                "attach" => {
                    attached = true;
                    (true, attach_data("s1"))
                }
                _ => (false, Value::Null),
            };
            stream
                .write_all(&frame(
                    &json!({ "kind": "outbound", "requestId": request_id, "outboundType": "response" }),
                    &json!({
                        "id": request_id,
                        "type": "response",
                        "command": command_type,
                        "success": success,
                        "data": data,
                    }),
                ))
                .expect("worker response");
        }
    }
    std::thread::sleep(Duration::from_millis(500));
    died.store(true, Ordering::SeqCst);
    let _ = stream.shutdown(std::net::Shutdown::Both);
}

/// The supervisor: it serves the session over a direct link until the
/// worker dies, refuses the one re-attach attempt the client's window
/// allows (by the active id, then by the durable id), then serves the
/// session again and answers its prompt.
// One scripted supervisor (the request loop and its reachability state);
// split, its arms would lose the state they share.
#[allow(clippy::too_many_lines)]
fn serve_supervisor(listener: &UnixListener, worker_socket: &Path, died: &AtomicBool) {
    let (stream, _) = listener.accept().expect("supervisor accept");
    let writer = Mutex::new(stream.try_clone().expect("clone supervisor socket"));
    let write = |value: &Value| {
        let mut line = serde_json::to_string(value).expect("serialize line");
        line.push('\n');
        let mut writer = writer.lock().expect("supervisor writer");
        let _ = writer.write_all(line.as_bytes());
    };
    write(&json!({
        "type": "daemon_hello",
        "protocol": { "name": "eukhe.daemon", "version": 7 },
        "serverCapabilities": ["direct_peer_transport"],
        "clientId": "mock",
    }));
    // The attaches refused since the worker died: the first attempt's two.
    let mut refused = 0_u32;
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
        let id = envelope["id"].as_str().unwrap_or_default().to_string();
        let command_type = envelope["command"]["type"]
            .as_str()
            .unwrap_or_default()
            .to_string();
        let reachable = !died.load(Ordering::SeqCst) || refused >= 2;
        match command_type.as_str() {
            "create" => write(&response(
                &id,
                "create",
                &json!({
                    "activeSessionId": "s1",
                    "id": "s1",
                    "sessionId": "sess-1",
                    "sessionFile": "/tmp/sess-1.jsonl",
                }),
            )),
            "get_direct_worker_transport" if !died.load(Ordering::SeqCst) => {
                let identity =
                    eukhe_types::platform::socket_identity(worker_socket).expect("worker socket");
                write(&response(
                    &id,
                    "get_direct_worker_transport",
                    &json!({
                        "purpose": "session_client",
                        "socketPath": worker_socket.to_string_lossy(),
                        "socketIdentity": { "dev": identity.dev, "ino": identity.ino },
                        "workerInstanceId": "inst-1",
                        "activeSessionId": "s1",
                        "grantId": "g1",
                        "token": "t",
                        "expiresAt": "2999-01-01T00:00:00.000Z",
                    }),
                ));
            }
            "attach" if !reachable => {
                refused += 1;
                write(&json!({
                    "type": "response",
                    "id": id,
                    "command": command_type,
                    "success": false,
                    "error": "Unknown active session: s1",
                }));
            }
            "get_direct_worker_transport" => write(&json!({
                "type": "response",
                "id": id,
                "command": command_type,
                "success": false,
                "error": "Session worker is not connected",
            })),
            "attach" => write(&response(&id, "attach", &attach_data("s1"))),
            "prompt" if reachable => {
                write(&response(&id, "prompt", &json!({})));
                let user = json!({
                    "role": "user",
                    "content": [{ "type": "text", "text": PROMPT }],
                    "timestamp": 2,
                });
                let answer = json!({
                    "role": "assistant",
                    "content": [{ "type": "text", "text": ANSWER }],
                    "api": "faux", "provider": "faux", "model": "faux-1",
                    "usage": {
                        "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 0,
                        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
                    },
                    "stopReason": "stop",
                    "timestamp": 3,
                });
                for event in [
                    json!({ "type": "agent_start" }),
                    json!({ "type": "turn_start" }),
                    json!({ "type": "message_start", "message": user }),
                    json!({ "type": "message_end", "message": user }),
                    json!({ "type": "message_start", "message": answer, "assistantMessageEvent": { "type": "start" } }),
                    json!({ "type": "message_end", "message": answer }),
                    json!({ "type": "turn_end", "message": answer, "toolResults": [] }),
                    json!({ "type": "agent_end", "messages": [] }),
                ] {
                    write(
                        &json!({ "type": "session_event", "activeSessionId": "s1", "event": event }),
                    );
                }
            }
            "prompt" => write(&json!({
                "type": "response",
                "id": id,
                "command": "prompt",
                "success": false,
                "error": "Unknown active session: s1",
            })),
            _ => write(&response(&id, &command_type, &json!({}))),
        }
    }
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
        prompt_stash: Arc::default(),
        session_has_children: false,
        restore_dock_focus: false,
        client_settings: None,
        dictation: None,
        daemon_launcher: None,
    }
}

#[test]
fn a_submit_after_the_reattach_window_reattaches_and_is_answered() {
    // The ambient TMUX variable adds a startup notice to the transcript.
    std::env::remove_var("TMUX");
    // The window allows one re-attach attempt; each test is its own process.
    std::env::set_var(RECONNECT_WINDOW_ENV, "0");
    let dir = tempfile::TempDir::new().expect("temp dir");
    let socket = dir.path().join("tui.sock");
    let worker_socket = dir.path().join("worker.sock");
    let supervisor_listener = UnixListener::bind(&socket).expect("bind supervisor");
    let worker_listener = UnixListener::bind(&worker_socket).expect("bind worker");
    let died = Arc::new(AtomicBool::new(false));
    let worker = {
        let died = Arc::clone(&died);
        std::thread::spawn(move || serve_worker(&worker_listener, &died))
    };
    let supervisor = {
        let died = Arc::clone(&died);
        std::thread::spawn(move || serve_supervisor(&supervisor_listener, &worker_socket, &died))
    };
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .expect("tokio runtime");
    let outcome = runtime
        .block_on(run_interactive(
            options(socket),
            UiMode::Headless(HeadlessPlan {
                steps: vec![
                    HeadlessStep::WaitRender {
                        needle: "Daemon reconnection failed".to_string(),
                        timeout_ms: 20_000,
                    },
                    HeadlessStep::Submit(PROMPT.to_string()),
                    HeadlessStep::WaitRender {
                        needle: ANSWER.to_string(),
                        timeout_ms: 20_000,
                    },
                ],
                width: 140,
                height: 40,
            }),
        ))
        .expect("the interactive run settles");
    worker.join().expect("mock worker finished");
    drop(supervisor);
    let last = outcome.frames.last().expect("a final frame");
    assert!(last.contains(ANSWER), "the prompt was answered:\n{last}");
    assert!(
        last.contains("Daemon reconnected"),
        "the submit re-attached the session:\n{last}"
    );
}
