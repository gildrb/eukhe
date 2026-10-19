//! A supervisor crash heals (audit F2): the supervisor dies by SIGKILL in
//! the middle of a run, the attached TUI's lost-daemon recovery relaunches
//! a daemon of this build through the CLI launcher (the code `eukhe` wires
//! as `CliLauncher`), the new supervisor adopts the live worker, and the run
//! finishes on it.
//!
//! The test has its own binary: the relaunched supervisor inherits this
//! process's environment (its agent dir), which a shared test binary
//! could change under it.
// Pedantic-gate dispositions for THIS test root: the crash flow is one
// linear harness script (the fn-length gate is style, not correctness),
// and its async test future is stack-resident by shape (boxing it for a
// lint tick is churn with no correctness gain).
#![allow(clippy::large_futures, clippy::too_many_lines)]

use std::future::Future;
use std::io::{BufRead, BufReader, Write};
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

use eukhe_tui::daemon_client::DaemonClient;
use eukhe_tui::interactive::{
    HeadlessPlan, HeadlessStep, InteractiveOptions, ModelSelection, SessionSelection, UiMode,
};
use eukhe_tui::saved_sessions::{DaemonLauncher, SharedDaemonLauncher};

#[path = "support/eukhe.rs"]
mod eukhe;

#[path = "support/durable_store.rs"]
mod durable_store;

use durable_store::{read_transcript, session_dirs, try_read_transcript, Transcript};

/// The texts of the stored model messages of `role`, in order.
fn role_texts(transcript: &Transcript, role: &str) -> Vec<String> {
    transcript
        .entries
        .iter()
        .filter_map(|entry| entry["model"].as_array())
        .flatten()
        .filter(|message| message["role"] == role)
        .filter_map(|message| {
            let content = &message["content"];
            content.as_str().map(str::to_owned).or_else(|| {
                content
                    .as_array()?
                    .iter()
                    .find_map(|block| block["text"].as_str().map(str::to_owned))
            })
        })
        .collect()
}

/// The faux generation's hold: long enough that the kill, the relaunch,
/// and the reattach all land inside the run.
const RUN_HOLD_MS: u64 = 20_000;

/// The bound of every observation wait in this test.
const WAIT_BOUND: Duration = Duration::from_secs(90);

/// The launcher the TUI's lost-daemon recovery calls: the CLI launch path
/// (`ensure_daemon_running_with`) with this build's `eukhe` binary as a
/// background caller, as `CliLauncher` runs it with the current executable.
struct BuildLauncher {
    socket: PathBuf,
    cwd: PathBuf,
    launches: Arc<AtomicUsize>,
}

impl DaemonLauncher for BuildLauncher {
    fn ensure(&self) -> impl Future<Output = anyhow::Result<()>> + Send {
        self.launches.fetch_add(1, Ordering::SeqCst);
        let (socket, cwd) = (self.socket.clone(), self.cwd.clone());
        async move {
            let exe = PathBuf::from(env!("CARGO_BIN_EXE_eukhe"));
            eukhe_cli::ensure_daemon_running_with(
                &exe,
                eukhe_tui::daemon_build::Build::THIS,
                &socket,
                &cwd,
                eukhe_tui::daemon_build::Caller::Background,
            )
            .await
            .map(drop)
        }
    }
}

/// Stops the daemon on `socket` by protocol (it stops the workers it
/// adopted) and waits for its exit, then SIGKILLs the `workers` that are
/// still alive. It runs on a failing test's unwind too, so the test leaks
/// no processes and the temp dir outlives every writer.
struct Teardown {
    socket: PathBuf,
    workers: Vec<u32>,
}

impl Drop for Teardown {
    fn drop(&mut self) {
        // A sync `shutdown` request (this runs inside the async test's
        // runtime). Best effort: the answer is the sync point, the
        // supervisor's exit the end.
        if let Ok(stream) = UnixStream::connect(&self.socket) {
            let _ = stream.set_read_timeout(Some(Duration::from_secs(10)));
            let writer = stream.try_clone();
            let mut reader = BufReader::new(stream);
            let mut hello = String::new();
            let _ = reader.read_line(&mut hello);
            let supervisor = serde_json::from_str::<serde_json::Value>(&hello)
                .ok()
                .and_then(|hello| hello["supervisorPid"].as_u64())
                .and_then(|pid| u32::try_from(pid).ok());
            let command = serde_json::json!({
                "type": "command",
                "id": "teardown-shutdown",
                "protocol": {
                    "name": eukhe_types::daemon::DAEMON_PROTOCOL_NAME,
                    "version": eukhe_types::daemon::DAEMON_PROTOCOL_VERSION,
                },
                "command": { "type": "shutdown" },
            });
            if let Ok(mut writer) = writer {
                let _ = writeln!(writer, "{command}");
                let mut response = String::new();
                let _ = reader.read_line(&mut response);
            }
            let deadline = Instant::now() + Duration::from_secs(10);
            while supervisor.is_some_and(process_alive) && Instant::now() < deadline {
                std::thread::sleep(Duration::from_millis(20));
            }
        }
        for pid in &self.workers {
            if let Ok(raw) = i32::try_from(*pid) {
                // Best effort: the worker may already be gone.
                let _ = nix::sys::signal::kill(
                    nix::unistd::Pid::from_raw(raw),
                    nix::sys::signal::Signal::SIGKILL,
                );
            }
        }
        let _ = std::fs::remove_file(&self.socket);
    }
}

/// The supervisor pid the daemon on `socket` greets with.
async fn supervisor_pid(socket: &Path) -> u32 {
    let (client, _events) = DaemonClient::connect(socket)
        .await
        .expect("connect the supervisor");
    let pid = client.hello()["supervisorPid"]
        .as_u64()
        .and_then(|pid| u32::try_from(pid).ok())
        .expect("the hello names the supervisor pid");
    client.close();
    pid
}

/// Liveness that ignores zombies.
fn process_alive(pid: u32) -> bool {
    std::fs::read_to_string(format!("/proc/{pid}/stat")).is_ok_and(|stat| {
        stat.rsplit_once(')')
            .and_then(|(_, rest)| rest.split_whitespace().next())
            .is_some_and(|state| !state.starts_with('Z') && !state.starts_with('X'))
    })
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_killed_supervisor_is_relaunched_and_the_run_finishes() {
    // The daemon binds only in a private (0700) directory.
    let dir = tempfile::Builder::new()
        .prefix("supervisor-crash-")
        .permissions(std::os::unix::fs::PermissionsExt::from_mode(0o700))
        .tempdir_in("/tmp")
        .expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    let socket = dir.path().join("daemon.sock");
    // Every supervisor of this test (the first one and the relaunch)
    // inherits this environment: the temp agent dir, this checkout's
    // kernel runtime, no ambient provider keys, and the short lost-exit
    // window (a worker of a failing run cannot outlive the test long).
    std::env::set_var("EUKHE_CODING_AGENT_DIR", &agent_dir);
    std::env::set_var(
        "EUKHE_KERNEL_PYTHON",
        eukhe::kernel_runtime::kernel_python(),
    );
    std::env::set_var(
        eukhe_daemon::worker::WORKER_SUPERVISOR_LOST_EXIT_MS_ENV,
        "15000",
    );
    for provider in eukhe_ai::providers::all::builtin_providers() {
        for var in eukhe_ai::env_api_keys::find_env_keys(&provider.id, None).unwrap_or_default() {
            std::env::remove_var(var);
        }
    }
    let script_path = dir.path().join("script.json");
    std::fs::write(
        &script_path,
        serde_json::json!({ "responses": [{ "text": "survived", "delayMs": RUN_HOLD_MS }] })
            .to_string(),
    )
    .expect("write script");

    let launch_count = Arc::new(AtomicUsize::new(0));
    let launcher = BuildLauncher {
        socket: socket.clone(),
        cwd: dir.path().to_path_buf(),
        launches: Arc::clone(&launch_count),
    };
    launcher.ensure().await.expect("start the first daemon");
    let first_supervisor = supervisor_pid(&socket).await;
    let mut teardown = Teardown {
        socket: socket.clone(),
        workers: Vec::new(),
    };

    // The crash, ordered by observation: once the run holds, SIGKILL the
    // supervisor (no graceful stop; its detached worker lives on).
    let kill_session_dir = session_dir.clone();
    let kill = tokio::spawn(async move {
        // The run holds once its prompt is in the storage.
        let deadline = Instant::now() + WAIT_BOUND;
        loop {
            let prompted = session_dirs(&kill_session_dir)
                .first()
                .is_some_and(|storage| {
                    try_read_transcript(storage)
                        .is_some_and(|transcript| role_texts(&transcript, "user") == ["go"])
                });
            if prompted {
                break;
            }
            assert!(Instant::now() < deadline, "the run never started");
            tokio::time::sleep(Duration::from_millis(20)).await;
        }
        // The session workers of the supervisor: its children whose
        // environment carries the worker role.
        let role = format!("{}=1", eukhe_daemon::worker::WORKER_ROLE_ENV);
        let mut workers = Vec::new();
        for entry in std::fs::read_dir("/proc").expect("read /proc").flatten() {
            let Ok(pid) = entry.file_name().to_string_lossy().parse::<u32>() else {
                continue;
            };
            let Ok(stat) = std::fs::read_to_string(format!("/proc/{pid}/stat")) else {
                continue;
            };
            // `comm` can hold spaces and parens: the fields follow the last ')'.
            let parent = stat
                .rsplit_once(')')
                .and_then(|(_, rest)| rest.split_whitespace().nth(1))
                .and_then(|parent| parent.parse::<u32>().ok());
            let worker = std::fs::read(format!("/proc/{pid}/environ")).is_ok_and(|environ| {
                environ
                    .split(|byte| *byte == 0)
                    .any(|entry| entry == role.as_bytes())
            });
            if parent == Some(first_supervisor) && worker {
                workers.push(pid);
            }
        }
        let raw = i32::try_from(first_supervisor).expect("pid fits i32");
        nix::sys::signal::kill(
            nix::unistd::Pid::from_raw(raw),
            nix::sys::signal::Signal::SIGKILL,
        )
        .expect("SIGKILL the supervisor");
        workers
    });

    let plan = HeadlessPlan {
        steps: vec![
            HeadlessStep::WaitRender {
                needle: "survived".to_string(),
                timeout_ms: 90_000,
            },
            HeadlessStep::WaitIdle { timeout_ms: 30_000 },
        ],
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
        initial_message: Some("go".to_string()),
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
        daemon_launcher: Some(SharedDaemonLauncher::new(launcher)),
    };
    let outcome = tokio::time::timeout(
        Duration::from_secs(300),
        eukhe_tui::interactive::run_interactive(options, UiMode::Headless(plan)),
    )
    .await
    .expect("the headless run ends")
    .expect("the headless run");
    let workers = kill.await.expect("the kill task");
    teardown.workers.clone_from(&workers);

    let rendered = outcome.frames.join("\n");
    assert!(
        rendered.contains("starting it again"),
        "the recovery relaunched the daemon:\n{rendered}"
    );
    assert!(
        launch_count.load(Ordering::SeqCst) >= 2,
        "the TUI recovery called the launcher"
    );
    let second_supervisor = supervisor_pid(&socket).await;
    assert_ne!(second_supervisor, first_supervisor, "a new supervisor runs");
    assert_eq!(outcome.last_assistant_text.as_deref(), Some("survived"));
    let storages = session_dirs(&session_dir);
    assert_eq!(storages.len(), 1, "one session: {storages:?}");
    let transcript = read_transcript(&storages[0]);
    // One prompt and one answer: the run finished once, nothing re-ran it.
    assert_eq!(role_texts(&transcript, "assistant"), ["survived"]);
    assert_eq!(
        role_texts(&transcript, "user")
            .iter()
            .filter(|text| *text == "go")
            .count(),
        1
    );
    // The new supervisor adopted the worker that outlived the crash: it
    // still runs (a replaced worker is stopped, a revived one is new).
    assert_eq!(workers.len(), 1, "one worker at the crash: {workers:?}");
    assert!(process_alive(workers[0]), "the worker was adopted");
    drop(teardown);
}
