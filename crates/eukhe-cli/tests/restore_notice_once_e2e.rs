//! A kernel restore notice shows once. A session's kernel holds a name;
//! then the session's worker is replaced `RESTARTS` times (the worker is
//! killed and the session opened again). Each new worker's kernel revives
//! the name and stores one `ipython_state_restored` notice, and the
//! attached TUI attaches to the new worker and rebuilds its transcript
//! from every stored message. The storage holds one notice for each
//! restore, and the TUI transcript (the inline scrollback, each rebuild
//! included) shows one restore row for each restore: an attach does not
//! show the notices of earlier restores again.
//!
//! The test has its own binary: it sets the process environment that
//! the in-process TUI reads.
// The test is one linear script (the fn-length gate is style, not
// correctness), and its async test future is stack-resident by shape.
#![allow(clippy::large_futures, clippy::too_many_lines)]

use std::io::{BufRead, BufReader, Write};
use std::os::unix::net::UnixStream;
use std::path::Path;
use std::sync::Arc;
use std::time::{Duration, Instant};

use eukhe_tui::interactive::{
    HeadlessPlan, HeadlessStep, InteractiveOptions, ModelSelection, SessionSelection, UiMode,
};

#[path = "support/eukhe.rs"]
mod eukhe;
#[path = "../../eukhe-daemon/tests/support/process.rs"]
mod process;
use eukhe::{daemon_mode_args, eukhe_command, scrub_provider_keys};
use process::Daemon;

#[path = "support/durable_store.rs"]
mod durable_store;
use durable_store::{session_dirs, try_read_transcript, Transcript};

/// The worker replacements (each one a restore of the kernel namespace).
const RESTARTS: usize = 3;

/// The bound of every observation wait in this test.
const WAIT_BOUND: Duration = Duration::from_secs(120);

/// The row the TUI shows for a restore notice.
const RESTORE_ROW: &str = "Restored Python kernel state";

/// The prompt the driver sends to the worker of replacement `k`: the TUI
/// shows it once it follows that worker.
fn cycle_prompt(k: usize) -> String {
    format!("cycle {k}")
}

/// The prompt the TUI sends back once it shows [`cycle_prompt`] `k`.
fn ack_prompt(k: usize) -> String {
    format!("ack {k}")
}

/// The stored transcript of the session under `session_dir`.
fn stored(session_dir: &Path) -> Option<Transcript> {
    session_dirs(session_dir)
        .first()
        .and_then(|storage| try_read_transcript(storage))
}

/// The restore notices stored in the session under `session_dir`.
fn stored_restores(session_dir: &Path) -> usize {
    stored(session_dir).map_or(0, |transcript| {
        transcript.custom_rows("ipython_state_restored").len()
    })
}

/// Whether a kernel snapshot of the session under `session_dir` saved `x`.
fn snapshot_holds_x(session_dir: &Path) -> bool {
    let Some(storage) = session_dirs(session_dir).into_iter().next() else {
        return false;
    };
    let Ok(kernels) = std::fs::read_dir(storage.join("kernels")) else {
        return false;
    };
    kernels.flatten().any(|kernel| {
        std::fs::read_to_string(eukhe_core::kernel::state_snapshot::manifest_path_in(
            kernel.path(),
        ))
        .ok()
        .and_then(|raw| serde_json::from_str::<serde_json::Value>(&raw).ok())
        .and_then(|manifest| {
            manifest["savedNames"]
                .as_array()
                .map(|names| names.iter().any(|name| name == "x"))
        })
        .unwrap_or(false)
    })
}

/// Poll `ready` until it holds; panic with `what` after [`WAIT_BOUND`].
fn wait_for(what: &str, mut ready: impl FnMut() -> bool) {
    let deadline = Instant::now() + WAIT_BOUND;
    while !ready() {
        assert!(Instant::now() < deadline, "timed out waiting for {what}");
        std::thread::sleep(Duration::from_millis(50));
    }
}

/// Send `command` to the daemon on `socket` and return its response.
fn request(socket: &Path, command: &serde_json::Value) -> serde_json::Value {
    let stream = UnixStream::connect(socket).expect("connect the daemon");
    stream
        .set_read_timeout(Some(WAIT_BOUND))
        .expect("set the read timeout");
    let mut writer = stream.try_clone().expect("clone the socket");
    let mut reader = BufReader::new(stream);
    let mut hello = String::new();
    reader.read_line(&mut hello).expect("read the hello");
    let line = serde_json::json!({
        "type": "command",
        "id": "driver",
        "protocol": {
            "name": eukhe_types::daemon::DAEMON_PROTOCOL_NAME,
            "version": eukhe_types::daemon::DAEMON_PROTOCOL_VERSION,
        },
        "command": command,
    });
    writeln!(writer, "{line}").expect("send the command");
    loop {
        let mut response = String::new();
        reader.read_line(&mut response).unwrap_or_else(|error| {
            // The daemon's own log says where the command stuck.
            let agent_dir = socket.parent().expect("the socket's dir").join("agent");
            let log =
                std::fs::read_to_string(eukhe_daemon::paths::daemon_log_path(socket, &agent_dir))
                    .unwrap_or_default();
            panic!("read the response to {command}: {error}\ndaemon log:\n{log}")
        });
        let response: serde_json::Value =
            serde_json::from_str(response.trim()).expect("parse a response");
        if response["id"] == "driver" {
            return response;
        }
    }
}

/// Send `command` and require its success.
fn command_ok(socket: &Path, command: &serde_json::Value) -> serde_json::Value {
    let response = request(socket, command);
    assert_eq!(response["success"], true, "{command}: {response}");
    response
}

/// The live session rows of the daemon's list.
fn live_rows(socket: &Path) -> Vec<serde_json::Value> {
    let listed = command_ok(socket, &serde_json::json!({ "type": "list" }));
    listed["data"]["sessions"]
        .as_array()
        .into_iter()
        .flatten()
        .filter(|row| row["lifecycle"] == "live")
        .cloned()
        .collect()
}

/// Replace the session's worker `RESTARTS` times. Replacement `k` waits
/// until the worker before it answered the TUI's last prompt (for `k > 1`
/// its acknowledgement of [`cycle_prompt`] `k - 1`), kills the worker,
/// opens the session again, waits for the new kernel's restore notice
/// and prompts the new worker with [`cycle_prompt`] `k`.
fn drive_restarts(socket: &Path, create_config: &serde_json::Value, session_dir: &Path) {
    wait_for("the kernel snapshot that saves x", || {
        snapshot_holds_x(session_dir)
    });
    for k in 1..=RESTARTS {
        // The TUI's last prompt (its acknowledgement of the worker
        // before) is answered: no turn runs when the worker dies.
        let prompt = if k == 1 {
            "set x".to_string()
        } else {
            ack_prompt(k - 1)
        };
        wait_for("the answer to the TUI's last prompt", || {
            stored(session_dir).is_some_and(|transcript| {
                let texts = transcript.chat_texts();
                texts
                    .iter()
                    .position(|text| *text == prompt)
                    .is_some_and(|at| texts[at + 1..].iter().any(|text| text == "x is set"))
            })
        });
        let mut row = serde_json::Value::Null;
        wait_for("one live session", || {
            if let [live] = live_rows(socket).as_slice() {
                row = live.clone();
            }
            !row.is_null()
        });
        let (active, file) = (row["id"].clone(), row["sessionFile"].clone());
        command_ok(
            socket,
            &serde_json::json!({ "type": "kill", "activeSessionId": active }),
        );
        wait_for("the killed worker to leave the list", || {
            live_rows(socket).iter().all(|row| row["id"] != active)
        });
        let created = command_ok(
            socket,
            &serde_json::json!({ "type": "create", "sessionPath": file, "config": create_config }),
        );
        let replacement = created["data"]["id"].clone();
        wait_for("the new worker in the list", || {
            live_rows(socket).iter().any(|row| row["id"] == replacement)
        });
        wait_for("the restore of the new worker", || {
            stored_restores(session_dir) == k
        });
        command_ok(
            socket,
            &serde_json::json!({
                "type": "prompt",
                "activeSessionId": replacement,
                "message": cycle_prompt(k),
            }),
        );
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn each_restore_notice_shows_once_across_reconnects() {
    // The daemon binds only in a private (0700) directory.
    let dir = tempfile::Builder::new()
        .prefix("restore-notice-")
        .permissions(std::os::unix::fs::PermissionsExt::from_mode(0o700))
        .tempdir_in("/tmp")
        .expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    let socket = dir.path().join("daemon.sock");
    // The in-process TUI reads the same agent dir as the daemon.
    std::env::set_var("EUKHE_CODING_AGENT_DIR", &agent_dir);
    let mut command = eukhe_command();
    daemon_mode_args(&mut command, &socket, &agent_dir);
    scrub_provider_keys(&mut command);
    let daemon = Daemon::spawn_listening(&mut command, &socket, Duration::from_secs(15));

    // A worker's first turn sets x; its later turns answer with text.
    let script_path = dir.path().join("script.json");
    std::fs::write(
        &script_path,
        serde_json::json!({
            "responses": [
                { "content": [
                    { "type": "toolCall", "name": "ipython", "arguments": { "code": "x = 41" } },
                ] },
                { "text": "x is set" },
            ],
            "repeatLastResponse": true,
        })
        .to_string(),
    )
    .expect("write script");
    let create_config = serde_json::json!({
        "cwd": dir.path().to_string_lossy(),
        "sessionDir": session_dir.to_string_lossy(),
        "script": script_path.to_string_lossy(),
    });

    let driver = {
        let (socket, session_dir) = (socket.clone(), session_dir.clone());
        tokio::task::spawn_blocking(move || drive_restarts(&socket, &create_config, &session_dir))
    };
    let mut steps = vec![HeadlessStep::SubmitAndSettle {
        text: "set x".to_string(),
        timeout_ms: 60_000,
    }];
    for k in 1..=RESTARTS {
        steps.push(HeadlessStep::WaitRender {
            needle: cycle_prompt(k),
            timeout_ms: 120_000,
        });
        steps.push(HeadlessStep::SubmitAndSettle {
            text: ack_prompt(k),
            timeout_ms: 60_000,
        });
    }
    let plan = HeadlessPlan {
        steps,
        width: 100,
        height: 30,
    };
    let options = InteractiveOptions {
        models: None,
        socket_path: socket.clone(),
        cwd: dir.path().to_path_buf(),
        session_dir: Some(session_dir.clone()),
        script_path: Some(script_path),
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
    };
    let outcome = tokio::time::timeout(
        Duration::from_secs(600),
        eukhe_tui::interactive::run_interactive(options, UiMode::Headless(plan)),
    )
    .await
    .expect("the headless run ends")
    .expect("the headless run");
    driver.await.expect("the restart driver");

    assert_eq!(
        stored_restores(&session_dir),
        RESTARTS,
        "one notice per restore"
    );
    // The last frame holds the whole inline scrollback (each transcript a
    // rebuild wrote) and the live area.
    let transcript = outcome
        .frames
        .last()
        .map(String::as_str)
        .unwrap_or_default();
    assert_eq!(
        transcript.matches(RESTORE_ROW).count(),
        RESTARTS,
        "each restore shows once:\n{transcript}"
    );
    drop(daemon);
}
