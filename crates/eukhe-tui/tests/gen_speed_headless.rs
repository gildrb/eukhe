//! Headless e2e for the status line's generation speed
//! (`terminal.showSpeed`): a mock supervisor plays a scripted provider
//! turn with timed events -- the prefill wait, the server's prompt progress
//! (llama.cpp), streamed deltas, and the settled message with its usage and
//! stream marks -- and the frames show each phase: `prefill <elapsed>s`,
//! `prefill p/n tokens`, `decode N tok/s`, then the exact summary.
// - the casts: timestamps in ms fit an i64 for centuries.
#![allow(clippy::cast_possible_truncation, clippy::cast_possible_wrap)]
// - the futures are bounded by the surface's lifetime; boxing them would
//   add an allocation to the steady-state loop.
#![allow(clippy::large_futures)]

use std::io::{BufRead, BufReader, Write};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::PathBuf;
use std::sync::{Arc, Mutex};
use std::time::Duration;

use eukhe_tui::interactive::{
    run_interactive, HeadlessPlan, HeadlessStep, InteractiveOptions, ModelSelection,
    SessionSelection, UiMode,
};
use serde_json::{json, Value};

/// The summary the settled message gives: 6,144 uncached prompt tokens
/// over a 2 s TTFT, 100 tokens after the first over 2 s of decode.
const SUMMARY: &str = "prefill 3072 tok/s (TTFT 2.0s) · decode 50.0 tok/s";

type Writer = Arc<Mutex<UnixStream>>;

fn write_json(writer: &Writer, value: &Value) {
    let mut line = serde_json::to_string(value).expect("serialize mock frame");
    line.push('\n');
    let mut stream = writer.lock().expect("mock writer");
    stream.write_all(line.as_bytes()).expect("write mock frame");
    stream.flush().expect("flush mock frame");
}

fn respond(writer: &Writer, id: &str, command: &str, data: &Value) {
    write_json(
        writer,
        &json!({ "type": "response", "id": id, "command": command, "success": true, "data": data }),
    );
}

fn now_ms() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |d| d.as_millis() as i64)
}

/// Serve one connection: attach an empty session; each prompt plays the
/// scripted turn on its own thread so requests keep their answers; a
/// `cvar` line answers `terminal.showSpeed` off.
fn serve(listener: &UnixListener) {
    let (stream, _) = listener.accept().expect("accept");
    let writer: Writer = Arc::new(Mutex::new(stream.try_clone().expect("clone mock socket")));
    let mut reader = BufReader::new(stream);
    write_json(
        &writer,
        &json!({
            "type": "daemon_hello",
            "protocol": { "name": "eukhe.daemon", "version": 7 },
            "serverCapabilities": [],
            "clientId": "mock",
        }),
    );
    let mut turns = Vec::new();
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
        let id = envelope["id"].as_str().unwrap_or("").to_string();
        let kind = envelope["command"]["type"]
            .as_str()
            .unwrap_or_default()
            .to_string();
        match kind.as_str() {
            "create" => respond(
                &writer,
                &id,
                "create",
                &json!({
                    "activeSessionId": "s1",
                    "id": "s1",
                    "sessionId": "sess-1",
                    "sessionFile": "/tmp/sess-1.jsonl",
                }),
            ),
            "attach" => respond(&writer, &id, "attach", &attach_data()),
            "cvar" => respond(
                &writer,
                &id,
                "cvar",
                &json!({ "values": [{ "id": "terminal.showSpeed", "value": false }] }),
            ),
            "prompt" => {
                respond(&writer, &id, "prompt", &json!({}));
                let writer = Arc::clone(&writer);
                turns.push(std::thread::spawn(move || play_turn(&writer)));
            }
            _ => respond(&writer, &id, &kind, &json!({})),
        }
    }
    for turn in turns {
        turn.join().expect("scripted turn");
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
                "sessionName": "speed session",
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

fn usage(input: u64, cache_read: u64, output: u64) -> Value {
    json!({
        "input": input, "output": output, "cacheRead": cache_read, "cacheWrite": 0,
        "totalTokens": input + cache_read + output,
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
    })
}

/// A streaming message: no usage yet.
fn assistant(text: &str, timestamp: i64) -> Value {
    json!({
        "role": "assistant",
        "content": [{ "type": "text", "text": text }],
        "api": "openai-completions",
        "provider": "llama-cpp",
        "model": "scripted-1",
        "usage": usage(0, 0, 0),
        "stopReason": "stop",
        "timestamp": timestamp,
    })
}

/// The scripted provider turn: 600 ms of prefill, the server's progress,
/// 600 ms more, then a delta every 100 ms for 800 ms, then the settled
/// message with its usage and stream marks.
fn play_turn(writer: &Writer) {
    let event = |payload: Value| {
        write_json(
            writer,
            &json!({ "type": "session_event", "activeSessionId": "s1", "event": payload }),
        );
    };
    let started = now_ms();
    event(json!({ "type": "turn_start" }));
    std::thread::sleep(Duration::from_millis(600));
    event(json!({
        "type": "prompt_progress",
        "progress": { "total": 8192, "cache": 2048, "processed": 4096, "timeMs": 600 },
    }));
    std::thread::sleep(Duration::from_millis(600));
    event(json!({
        "type": "message_start",
        "message": assistant("", started),
        "assistantMessageEvent": { "type": "start" },
    }));
    let mut text = String::new();
    for _ in 0..8 {
        text.push_str("tok tok tok tok tok tok tok tok ");
        event(json!({
            "type": "message_update",
            "message": assistant(&text, started),
            "assistantMessageEvent": { "type": "text_delta", "delta": "tok " },
        }));
        std::thread::sleep(Duration::from_millis(100));
    }
    let mut settled = assistant(&text, started);
    settled["usage"] = usage(6144, 2048, 101);
    settled["timing"] = json!({ "firstByteMs": 300, "firstTokenMs": 2000, "lastTokenMs": 4000 });
    event(json!({ "type": "message_end", "message": settled }));
    event(json!({ "type": "turn_end" }));
    event(json!({ "type": "agent_end", "messages": [] }));
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
    }
}

fn run_plan(steps: Vec<HeadlessStep>) -> Vec<String> {
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
        steps,
        width: 120,
        height: 30,
    };
    let outcome = runtime
        .block_on(run_interactive(options(socket), UiMode::Headless(plan)))
        .expect("interactive run");
    handle.join().expect("mock supervisor finished");
    outcome.frames
}

fn wait_render(needle: &str) -> HeadlessStep {
    HeadlessStep::WaitRender {
        needle: needle.to_string(),
        timeout_ms: 10_000,
    }
}

/// The status line row of `frame` that shows the speed, trimmed.
fn speed_row(frame: &str, needle: &str) -> Option<String> {
    frame
        .lines()
        .find(|line| line.contains(needle))
        .map(|line| line.trim().to_string())
}

/// Each phase shows on the status line in turn: the prefill clock, the
/// server's progress, the live decode rate (no TTFT yet), and the exact
/// summary from the usage and the stream marks, which stays after the
/// turn.
#[test]
fn the_status_line_shows_prefill_progress_decode_and_the_summary() {
    let frames = run_plan(vec![
        HeadlessStep::Submit("hello".to_string()),
        wait_render("prefill 0."),
        wait_render("prefill 4096/8192 tokens"),
        wait_render(" tok/s"),
        wait_render(SUMMARY),
        HeadlessStep::WaitIdle { timeout_ms: 10_000 },
        HeadlessStep::WaitMs(100),
    ]);
    let all = frames.join("\n");
    let first = |needle: &str| {
        frames
            .iter()
            .find_map(|frame| speed_row(frame, needle))
            .unwrap_or_else(|| panic!("no frame shows {needle:?}:\n{all}"))
    };
    let prefill = first("prefill 0.");
    let progress = first("prefill 4096/8192 tokens");
    let decode = frames
        .iter()
        .find_map(|frame| {
            frame
                .lines()
                .find(|line| line.contains("decode ") && line.contains(" tok/s"))
                .filter(|line| !line.contains("TTFT"))
                .map(|line| line.trim().to_string())
        })
        .unwrap_or_else(|| panic!("no frame shows the live decode rate:\n{all}"));
    let summary = first(SUMMARY);
    eprintln!("prefill:  {prefill}\nprogress: {progress}\ndecode:   {decode}\nsummary:  {summary}");
    let last = frames.last().expect("frames");
    assert!(
        last.contains(SUMMARY),
        "the summary stays after the turn:\n{last}"
    );
}

/// `/toggle terminal.showSpeed` off hides the segment at once: the turn
/// after it shows no phase and no summary.
#[test]
fn show_speed_off_hides_the_segment() {
    let frames = run_plan(vec![
        HeadlessStep::Submit("/toggle terminal.showSpeed".to_string()),
        wait_render("terminal.showSpeed = false"),
        HeadlessStep::Submit("hello".to_string()),
        HeadlessStep::WaitIdle { timeout_ms: 10_000 },
        HeadlessStep::WaitMs(100),
    ]);
    let all = frames.join("\n");
    assert!(all.contains("tok tok"), "the turn streamed:\n{all}");
    assert!(
        !all.contains("prefill") && !all.contains("decode"),
        "no speed segment renders:\n{all}"
    );
}
