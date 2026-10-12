//! Headless e2e for the agent family in the inline client: `@worker-1
//! message` goes to that agent (steered, it is generating) and never to
//! the main model, an unknown `@name` is an error row with the text kept
//! in the editor, `/agents` prints the family as tree rows, and a relayed
//! peer message lands as a dim `from -> to:` row.
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

fn child(id: &str, name: &str) -> Value {
    json!({
        "sessionId": id,
        "activeSessionId": format!("{id}-live"),
        "sessionName": name,
        "runtimeKind": "subagent",
        "rlmChildId": format!("sub-{id}"),
        "rlmDepth": 1,
        "parentActiveSessionId": "s1",
        "parentSessionId": "sess-1",
    })
}

fn roster() -> Value {
    let mut busy = child("c1", "worker-1");
    busy["isStreaming"] = json!(true);
    busy["model"] = json!("elpis/elpis-fast");
    busy["admission"] = json!("generating");
    busy["note"] = json!("triaged the flaky test");
    json!([
        {
            "agentId": "s1",
            "status": "idle",
            "summary": {
                "sessionId": "sess-1",
                "activeSessionId": "s1",
                "sessionName": "lead",
                "runtimeKind": "top-level",
            },
        },
        { "agentId": "c1", "status": "running", "summary": busy },
        { "agentId": "c2", "status": "idle", "summary": child("c2", "worker-2") },
    ])
}

/// Serve one connection: the hello, the attach snapshot, the roster, and
/// an empty success for everything else; every `prompt` is recorded, and
/// the one to `worker-1` is followed by a relayed peer message.
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
    let mut prompts = Vec::new();
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
            "roster_subscribe" => json!({ "roster": roster() }),
            _ => json!({}),
        };
        if command_type == "prompt" {
            prompts.push(command.clone());
        }
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
        if command_type == "prompt" {
            write_json(
                &mut writer,
                &json!({
                    "type": "session_event",
                    "activeSessionId": "s1",
                    "event": {
                        "type": "agent_relay",
                        "from": "worker-1",
                        "to": "worker-2",
                        "text": "found the bug in parse.rs\nfix incoming",
                    },
                }),
            );
        }
    }
    prompts
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
                { "role": "assistant", "content": "settled answer", "provider": "scripted", "model": "faux-1", "timestamp": 2 },
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

#[test]
fn at_name_talks_to_an_agent_and_agents_lists_the_family() {
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
            wait("settled answer"),
            HeadlessStep::Submit("@worker-1 check the tests".to_string()),
            wait("you -> worker-1: check the tests"),
            // The relay the mock pushes after the delivery: its first
            // line, dim, display only.
            wait("worker-1 -> worker-2: found the bug in parse.rs..."),
            HeadlessStep::Submit("/agents".to_string()),
            wait("agents: 2 (1 running)"),
            wait("|- worker-1  running (generating)  depth 1  elpis-fast  triaged the flaky test"),
            wait("`- worker-2  idle                  depth 1  -"),
            HeadlessStep::Submit("@nobody hello".to_string()),
            wait("Error: No agent named @nobody in this session (/agents lists them)"),
            // The draft stays in the editor.
            wait("@nobody hello"),
        ],
        width: 200,
        height: 40,
    };
    let frames = runtime
        .block_on(run_interactive(options(socket), UiMode::Headless(plan)))
        .expect("interactive run")
        .frames;
    let prompts = handle.join().expect("mock supervisor finished");
    assert!(
        frames
            .iter()
            .all(|frame| !frame.contains("timed out waiting")),
        "every render condition held:\n{}",
        frames.join("\n---frame---\n")
    );
    // One prompt went out, to worker-1 and steered (it is generating),
    // naming this session as the one its answer returns to; the main
    // model never saw the `@` messages.
    assert_eq!(
        prompts,
        vec![json!({
            "type": "prompt",
            "activeSessionId": "c1-live",
            "message": "check the tests",
            "streamingBehavior": "steer",
            "replyTo": "s1",
        })]
    );
}
