//! Headless e2e for dictation into the draft: the
//! `binds.cfg` keys of `app.stt.toggle` and `app.stt.pushToTalk` start a
//! take, the status line shows it, the fake recorder's WAV goes to the
//! fake transcriber, and the text lands in the editor draft. Esc cancels
//! a take; a failure and a disabled `stt.enabled` show as rows.
#![cfg(unix)]

use std::io::{BufRead, BufReader, Write};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use crossterm::event::{KeyCode, KeyEvent, KeyModifiers};
use eukhe_tui::dictation::{wav_bytes, Dictation, DictationFuture, Recorder, Transcriber};
use eukhe_tui::interactive::{
    run_interactive, HeadlessPlan, HeadlessStep, InteractiveOptions, ModelSelection,
    SessionSelection, UiMode,
};
use serde_json::{json, Value};
use tokio::sync::oneshot;

const BARRIER_TIMEOUT_MS: u64 = 5000;
const TRANSCRIPT: &str = "hello from the fake mic";
const RECORDING: &str = "[REC] recording, esc cancels";

/// Serve one client: attach answers with an empty session, `cvar`
/// answers with `stt.enabled = stt_enabled`, and every other command
/// gets one success response.
fn serve(listener: &UnixListener, stt_enabled: bool) {
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
        let data = match command_type.as_str() {
            "attach" => json!({
                "activeSessionId": "s1",
                "snapshot": {
                    "activeSessionId": "s1",
                    "summary": { "id": "s1", "cwd": "/tmp" },
                    "state": { "sessionId": "sess-1", "isStreaming": false },
                    "messages": [],
                    "lastEventSequence": 0,
                },
            }),
            "cvar" => json!({
                "values": [
                    { "id": "retry.enabled", "value": true },
                    { "id": "stt.enabled", "value": stt_enabled },
                ],
            }),
            _ => json!({
                "activeSessionId": "s1",
                "id": "s1",
                "sessionId": "sess-1",
                "sessionFile": "/tmp/sess-1.jsonl",
            }),
        };
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
}

fn write_json(writer: &mut UnixStream, value: &Value) {
    let mut line = serde_json::to_string(value).expect("serialize mock frame");
    line.push('\n');
    writer.write_all(line.as_bytes()).expect("write mock frame");
    writer.flush().expect("flush mock frame");
}

/// Records one sample until the stop, then writes the WAV.
struct FakeRecorder;

impl Recorder for FakeRecorder {
    fn record(&self, wav: PathBuf, stop: oneshot::Receiver<()>) -> DictationFuture<()> {
        Box::pin(async move {
            let _ = stop.await;
            tokio::fs::write(&wav, wav_bytes(&[1, 0]))
                .await
                .map_err(|error| error.to_string())
        })
    }
}

/// Answers `reply` for the recorder's WAV (anything else is an error),
/// and counts its calls.
struct FakeTranscriber {
    reply: Result<String, String>,
    calls: Arc<AtomicUsize>,
}

impl Transcriber for FakeTranscriber {
    fn transcribe(&self, wav: PathBuf) -> DictationFuture<String> {
        self.calls.fetch_add(1, Ordering::SeqCst);
        let reply = self.reply.clone();
        Box::pin(async move {
            let bytes = tokio::fs::read(&wav)
                .await
                .map_err(|error| error.to_string())?;
            if bytes != wav_bytes(&[1, 0]) {
                return Err("not the recorder's WAV".to_owned());
            }
            reply
        })
    }
}

fn options(socket: PathBuf, agent_dir: &Path, dictation: Dictation) -> InteractiveOptions {
    std::fs::write(
        agent_dir.join("binds.cfg"),
        "bind f8 \"action app.stt.toggle\"\nbind f9 \"action app.stt.pushToTalk\"\n",
    )
    .expect("write binds.cfg");
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
        keybindings: eukhe_tui::keybindings::KeybindingsManager::create(agent_dir),
        session_rlm_depth: None,
        prompt_stash: std::sync::Arc::default(),
        session_has_children: false,
        restore_dock_focus: false,
        client_settings: None,
        dictation: Some(dictation),
        daemon_launcher: None,
    }
}

fn key(code: KeyCode) -> HeadlessStep {
    HeadlessStep::Key(KeyEvent::new(code, KeyModifiers::NONE))
}

fn wait(needle: &str) -> HeadlessStep {
    HeadlessStep::WaitRender {
        needle: needle.to_string(),
        timeout_ms: BARRIER_TIMEOUT_MS,
    }
}

/// What a run showed: every frame, and the transcriber's call count.
struct Run {
    frames: Vec<String>,
    transcriptions: usize,
}

impl Run {
    fn last(&self) -> &str {
        self.frames.last().expect("final frame")
    }

    fn any(&self, needle: &str) -> bool {
        self.frames.iter().any(|frame| frame.contains(needle))
    }
}

fn run(stt_enabled: bool, reply: Result<String, String>, steps: Vec<HeadlessStep>) -> Run {
    // The ambient TMUX variable adds a startup notice; scrub it.
    std::env::remove_var("TMUX");
    let dir = tempfile::TempDir::new().expect("temp dir");
    let socket = dir.path().join("tui.sock");
    let listener = UnixListener::bind(&socket).expect("bind mock socket");
    let handle = std::thread::spawn(move || serve(&listener, stt_enabled));
    let calls = Arc::new(AtomicUsize::new(0));
    let dictation = Dictation {
        recorder: Arc::new(FakeRecorder),
        transcriber: Arc::new(FakeTranscriber {
            reply,
            calls: Arc::clone(&calls),
        }),
    };
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .expect("tokio runtime");
    let plan = HeadlessPlan {
        steps,
        width: 140,
        height: 30,
    };
    let outcome = runtime
        .block_on(run_interactive(
            options(socket, dir.path(), dictation),
            UiMode::Headless(plan),
        ))
        .expect("interactive run");
    drop(runtime);
    handle.join().expect("mock supervisor finished");
    let frames = outcome.frames;
    let all = frames.join("\n");
    assert!(
        !all.contains("timed out waiting"),
        "a render barrier timed out:\n{all}"
    );
    Run {
        frames,
        transcriptions: calls.load(Ordering::SeqCst),
    }
}

#[test]
fn the_toggle_key_records_until_its_next_press_and_types_the_transcript() {
    let run = run(
        true,
        Ok(TRANSCRIPT.to_owned()),
        vec![
            HeadlessStep::Type("note: ".to_string()),
            key(KeyCode::F(8)),
            wait(RECORDING),
            key(KeyCode::F(8)),
            wait(&format!("note: {TRANSCRIPT}")),
        ],
    );
    assert_eq!(
        (
            run.any(RECORDING),
            run.last().contains(&format!("note: {TRANSCRIPT}")),
            run.last().contains("[REC]") || run.last().contains("[STT]"),
            run.transcriptions,
        ),
        (true, true, false, 1),
        "{}",
        run.last()
    );
}

#[test]
fn the_push_to_talk_key_records_while_it_is_held() {
    // One press and no auto-repeat: the hold ends at the release window.
    let run = run(
        true,
        Ok(TRANSCRIPT.to_owned()),
        vec![key(KeyCode::F(9)), wait(RECORDING), wait(TRANSCRIPT)],
    );
    assert_eq!(
        (
            run.last().contains(TRANSCRIPT),
            run.last().contains("[REC]"),
            run.transcriptions
        ),
        (true, false, 1),
        "{}",
        run.last()
    );
}

#[test]
fn escape_cancels_a_take_before_it_transcribes() {
    let run = run(
        true,
        Ok(TRANSCRIPT.to_owned()),
        vec![
            key(KeyCode::F(8)),
            wait(RECORDING),
            key(KeyCode::Esc),
            wait("Dictation cancelled"),
        ],
    );
    assert_eq!(
        (
            run.last().contains("[REC]"),
            run.last().contains(TRANSCRIPT),
            run.transcriptions
        ),
        (false, false, 0),
        "{}",
        run.last()
    );
}

#[test]
fn a_transcription_failure_shows_an_error_row() {
    let run = run(
        true,
        Err("no model of the dictation chain is installed".to_owned()),
        vec![
            key(KeyCode::F(8)),
            wait(RECORDING),
            key(KeyCode::F(8)),
            wait("Dictation failed: no model of the dictation chain is installed"),
        ],
    );
    assert_eq!(
        (run.last().contains("[REC]"), run.transcriptions),
        (false, 1),
        "{}",
        run.last()
    );
}

#[test]
fn a_dictation_key_with_stt_off_says_how_to_turn_it_on() {
    let run = run(
        false,
        Ok(TRANSCRIPT.to_owned()),
        vec![
            key(KeyCode::F(8)),
            wait("Dictation is off. Turn it on with /set stt.enabled true"),
        ],
    );
    assert_eq!(
        (run.any("[REC]"), run.transcriptions),
        (false, 0),
        "{}",
        run.last()
    );
}
