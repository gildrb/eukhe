//! Headless e2e for an attach while the reply streams (a TUI killed mid-reply, then
//! `--resume`): the attach snapshot carries the in-flight partial reply, and the frames past
//! its cursor continue that reply in place, so the transcript shows the reply once.
#![cfg(unix)]

use std::io::{BufRead, BufReader, Write};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::PathBuf;

use eukhe_tui::interactive::{
    run_interactive, HeadlessPlan, HeadlessStep, InteractiveOptions, ModelSelection,
    SessionSelection, UiMode,
};
use serde_json::{json, Value};

/// The reply the worker streams: its first words are in the attach snapshot, the rest arrive
/// after the attach.
const WORDS: [&str; 6] = ["REPLYSTART", "w0", "w1", "w2", "w3", "REPLYEND"];
/// The words the snapshot's partial already holds.
const SNAPSHOT_WORDS: usize = 3;
/// The snapshot's event sequence: the live frames continue past it.
const SNAPSHOT_SEQUENCE: u64 = 40;

/// Serve one client: attach answers with the mid-reply snapshot and streams the rest of the
/// reply behind it; every other command gets one success response.
fn serve(listener: &UnixListener) {
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
        let command_type = envelope
            .get("command")
            .and_then(|command| command.get("type"))
            .and_then(Value::as_str)
            .unwrap_or_default()
            .to_string();
        if command_type == "attach" {
            write_json(&mut writer, &attach_data(id));
            stream_rest(&mut writer);
            continue;
        }
        // create, get_commands, get_session_stats, detach: one success covers all.
        write_json(
            &mut writer,
            &json!({
                "type": "response",
                "id": id,
                "command": command_type,
                "success": true,
                "data": {
                    "activeSessionId": "s1",
                    "id": "s1",
                    "sessionId": "sess-1",
                    "sessionFile": "/tmp/sess-1.jsonl",
                },
            }),
        );
    }
}

/// The assistant message holding the reply's first `words` words.
fn reply(words: usize) -> Value {
    json!({
        "role": "assistant",
        "content": [{ "type": "text", "text": WORDS[..words].join(" ") }],
        "api": "scripted",
        "provider": "scripted",
        "model": "faux-1",
        "usage": {
            "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 0,
            "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
        },
        "stopReason": "stop",
        "timestamp": 2,
    })
}

/// The frames past the snapshot's cursor: one `message_update` per further word, the
/// reply's `message_end`, then the turn's and the run's ends.
fn stream_rest(writer: &mut UnixStream) {
    let mut sequence = SNAPSHOT_SEQUENCE;
    let mut event = |payload: Value| {
        sequence += 1;
        json!({
            "type": "session_event",
            "activeSessionId": "s1",
            "event": payload,
            "meta": { "sequence": sequence },
        })
    };
    let mut frames = Vec::new();
    for words in SNAPSHOT_WORDS + 1..=WORDS.len() {
        frames.push(event(json!({
            "type": "message_update",
            "message": reply(words),
            "assistantMessageEvent": {
                "type": "text_delta",
                "delta": format!(" {}", WORDS[words - 1]),
            },
        })));
    }
    frames.push(event(
        json!({ "type": "message_end", "message": reply(WORDS.len()) }),
    ));
    frames.push(event(json!({ "type": "turn_end" })));
    frames.push(event(json!({ "type": "agent_end", "messages": [] })));
    for frame in &frames {
        write_json(writer, frame);
    }
}

fn write_json(writer: &mut UnixStream, value: &Value) {
    let mut line = serde_json::to_string(value).expect("serialize mock frame");
    line.push('\n');
    writer.write_all(line.as_bytes()).expect("write mock frame");
    writer.flush().expect("flush mock frame");
}

/// The attach result mid-reply: the run is open, and the daemon appended the in-flight
/// partial reply after the prompt.
fn attach_data(id: &str) -> Value {
    json!({
        "type": "response",
        "id": id,
        "command": "attach",
        "success": true,
        "data": {
            "activeSessionId": "s1",
            "snapshot": {
                "activeSessionId": "s1",
                "summary": { "id": "s1", "cwd": "/tmp" },
                "state": {
                    "sessionId": "sess-1",
                    "sessionName": "streaming session",
                    "isStreaming": true,
                },
                "messages": [
                    { "role": "user", "content": "go now", "timestamp": 1 },
                    reply(SNAPSHOT_WORDS),
                ],
                "lastEventSequence": SNAPSHOT_SEQUENCE,
            },
        },
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

/// The partial reply in the attach snapshot and the frames that finish it make one message:
/// the finished reply shows, and its first word shows once.
#[test]
fn an_attach_mid_reply_continues_the_partial_reply_in_place() {
    // Scrub the ambient TMUX variable: its startup notice must not reach the frames.
    std::env::remove_var("TMUX");
    let dir = tempfile::TempDir::new().expect("temp dir");
    let socket = dir.path().join("tui.sock");
    let listener = UnixListener::bind(&socket).expect("bind mock socket");
    let handle = std::thread::spawn(move || serve(&listener));
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .expect("tokio runtime");
    let plan = HeadlessPlan {
        steps: vec![HeadlessStep::WaitRender {
            needle: WORDS.join(" "),
            timeout_ms: 10_000,
        }],
        width: 100,
        height: 30,
    };
    let outcome = runtime
        .block_on(run_interactive(options(socket), UiMode::Headless(plan)))
        .expect("interactive run");
    handle.join().expect("mock supervisor finished");
    let last = outcome.frames.last().expect("a rendered frame");
    assert!(
        last.contains(&WORDS.join(" ")),
        "the finished reply never rendered:\n{last}"
    );
    assert_eq!(
        last.matches(WORDS[0]).count(),
        1,
        "the reply shows more than once:\n{last}"
    );
}
