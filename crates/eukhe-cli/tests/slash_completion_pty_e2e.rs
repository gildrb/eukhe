//! Real-pty e2e for slash-command completion: the product's terminal
//! renderer runs on a pty over a mock supervisor whose session holds one
//! step treated as not run after a crash. Typing `/bud` shows `/budget` with its
//! description, Tab completes it and lists its words, `set ` lists the
//! budget keys, `ti` + Tab completes `time=` with the ghost hint of its
//! value, and `/effects ran ` lists the session's real effect id.

use std::io::{BufRead, Read, Write};
use std::os::fd::{AsRawFd, OwnedFd};
use std::os::unix::process::CommandExt;
use std::path::PathBuf;
use std::process::{Child, Command, Stdio};
use std::time::{Duration, Instant};

use nix::fcntl::{fcntl, FcntlArg::F_SETFL, OFlag};
use nix::pty::{openpty, Winsize};
use serde_json::{json, Value};

use eukhe_tui::interactive::{
    run_interactive, InteractiveOptions, ModelSelection, SessionSelection, UiMode,
};

const CHILD_SOCKET_ENV: &str = "EUKHE_SLASH_COMPLETION_CHILD_SOCKET";

/// The step treated as not run that the session's ledger holds.
const EFFECT_ID: &str = "toolu_01AbC";
const EFFECT_WHAT: &str = "bash: make deploy";

/// The child half: the real interactive loop in terminal mode against the
/// parent's mock supervisor. Without `CHILD_SOCKET_ENV` it does nothing:
/// only the parent test drives it.
#[test]
fn slash_completion_child_mode() {
    let Ok(socket) = std::env::var(CHILD_SOCKET_ENV) else {
        return;
    };
    let runtime = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .expect("tokio runtime");
    let _ = runtime.block_on(run_interactive(
        child_options(PathBuf::from(socket)),
        UiMode::Terminal,
    ));
}

#[test]
fn slash_completion_shows_words_keys_hints_and_live_ids() {
    if nix::unistd::tcgetpgrp(std::io::stdin()).is_err() {
        eprintln!(
            "no controlling-terminal session on the runner (tcgetpgrp(fd 0) failed); \
             the slash completion e2e needs one to drive the pty child"
        );
        return;
    }
    nix::unistd::setsid().expect("a fresh session for the harness");
    let mut harness = Harness::start();
    harness.wait("settled answer", "the transcript painted");

    harness.type_and_wait(
        "/bud",
        "Show, set or add",
        "the budget row and its description",
    );
    harness.type_and_wait(
        "\t",
        "Give the session a budget",
        "budget's words after Tab",
    );
    harness.type_and_wait("set ", "Money: 1.50", "the budget keys below set");
    harness.type_and_wait("ti", "Work time: 90s", "time= the one key ti names");
    harness.type_and_wait("\t", "<duration>", "the ghost hint of time='s value");

    let erase = "\x7f".repeat("/budget set time=".len());
    harness.type_and_wait(
        &format!("{erase}/effects ran "),
        EFFECT_ID,
        "the session's open effect id",
    );
    harness.wait(EFFECT_WHAT, "the effect's description");
    harness.finish();
}

struct Harness {
    child: Child,
    _server: std::thread::JoinHandle<()>,
    master: std::fs::File,
    output: Vec<u8>,
}

impl Harness {
    fn start() -> Harness {
        let dir = tempfile::TempDir::new().expect("temp dir");
        let socket = dir.path().join("tui.sock");
        let listener = std::os::unix::net::UnixListener::bind(&socket).expect("bind mock socket");
        let server = std::thread::spawn(move || serve(&listener));
        let pty = openpty(
            Some(&Winsize {
                ws_row: 30,
                ws_col: 100,
                ws_xpixel: 0,
                ws_ypixel: 0,
            }),
            None,
        )
        .expect("open pty");
        let stdio = || -> Stdio { pty.slave.try_clone().expect("clone pty slave").into() };
        let child = Command::new(std::env::current_exe().expect("test binary"))
            .arg("--exact")
            .arg("slash_completion_child_mode")
            .env(CHILD_SOCKET_ENV, &socket)
            .env_remove("TMUX")
            .stdin(stdio())
            .stdout(stdio())
            .stderr(stdio())
            .process_group(0)
            .spawn()
            .expect("spawn child");
        // The child holds the socket for the whole test; the tree dies
        // with it at teardown.
        std::mem::forget(dir);
        let master: OwnedFd = pty.master;
        fcntl(master.as_raw_fd(), F_SETFL(OFlag::O_NONBLOCK)).expect("non-blocking pty master");
        Harness {
            child,
            _server: server,
            master: master.into(),
            output: Vec::new(),
        }
    }

    /// Read the pty until `needle` shows after byte `mark`.
    fn wait_from(&mut self, mark: usize, needle: &str, what: &str) {
        let deadline = Instant::now() + Duration::from_secs(30);
        while !contains(&self.output[mark..], needle.as_bytes()) {
            let mut buffer = [0u8; 8192];
            if let Ok(n) = self.master.read(&mut buffer) {
                self.output.extend_from_slice(&buffer[..n]);
            }
            assert!(
                Instant::now() < deadline,
                "timeout waiting for {what} ({needle:?}); pty since mark:\n{}",
                String::from_utf8_lossy(&self.output[mark..])
            );
            std::thread::sleep(Duration::from_millis(20));
        }
    }

    fn wait(&mut self, needle: &str, what: &str) {
        self.wait_from(0, needle, what);
    }

    fn type_and_wait(&mut self, keys: &str, needle: &str, what: &str) {
        let mark = self.output.len();
        self.master.write_all(keys.as_bytes()).expect("type keys");
        self.wait_from(mark, needle, what);
    }

    fn finish(mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

fn contains(haystack: &[u8], needle: &[u8]) -> bool {
    haystack
        .windows(needle.len())
        .any(|window| window == needle)
}

fn child_options(socket: PathBuf) -> InteractiveOptions {
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
        restart: None,
    }
}

/// The mock supervisor: the hello, the attach of one session with a
/// settled exchange and one open effect, and an empty success for every
/// other command.
fn serve(listener: &std::os::unix::net::UnixListener) {
    let Ok((stream, _)) = listener.accept() else {
        return;
    };
    let mut writer = stream.try_clone().expect("clone mock socket");
    let mut reader = std::io::BufReader::new(stream);
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
        let command = envelope
            .get("command")
            .and_then(|command| command.get("type"))
            .and_then(Value::as_str)
            .unwrap_or_default()
            .to_string();
        let data = if command == "attach" {
            attach_data()
        } else {
            json!({})
        };
        write_json(
            &mut writer,
            &json!({
                "type": "response",
                "id": id,
                "command": command,
                "success": true,
                "data": data,
            }),
        );
    }
}

fn write_json(writer: &mut std::os::unix::net::UnixStream, value: &Value) {
    let mut line = serde_json::to_string(value).expect("serialize mock frame");
    line.push('\n');
    writer.write_all(line.as_bytes()).expect("write mock frame");
    writer.flush().expect("flush mock frame");
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
                "sessionName": "completion probe",
                "model": "faux-1",
                "isStreaming": false,
                "isCompacting": false,
                "sessionActions": { "queuedCount": 0, "steering": [], "followUps": [] },
                "unknownEffects": [
                    { "id": EFFECT_ID, "kind": "tool", "what": EFFECT_WHAT, "at": 1.0 },
                ],
            },
            "messages": [
                { "role": "user", "content": "hello", "timestamp": 1 },
                {
                    "role": "assistant",
                    "content": [{ "type": "text", "text": "settled answer" }],
                    "api": "openai-completions",
                    "provider": "scripted",
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
