// The Tier-C/D ruling (fleet-uniform, 2026-09-28): stack-resident futures
// by design on hot paths (boxing 130 fns is allocation-churn with zero
// correctness gain); the fn-length threshold is a style gate, not
// correctness (the harness fns are intentionally linear); 64-bit targets -
// the narrowing sits at OS/protocol boundaries where the values are
// bounded (pid syscalls, epoch/elapsed milliseconds, calendar math,
// guarded parses), and checked conversions would add panic paths where
// silent wrap was deliberate (the one genuinely-suspect family, args.rs's
// parse_positive_u32 lacking its u32::MAX bound, is flagged in the lane
// dossier for the conductor).
#![allow(
    clippy::large_futures,
    clippy::too_many_lines,
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss,
    clippy::cast_precision_loss
)]

//! End-to-end verifier for the interactive TUI: spawn the real supervisor
//! (`eukhe --mode daemon`, the same binary the interactive runtime
//! launches when no daemon is running), then drive the TUI headlessly
//! against a scripted daemon session — create/attach, prompt, streamed
//! assistant output, session list, and a session switch — and assert on the
//! rendered frames plus the daemon-side session state.
//!
//! The scripted engine seam (`create` config `script`) is the same faux
//! provider contract `eukhe-daemon/tests/supervisor_e2e/main.rs` uses; the product
//! never sets it.

use std::fmt::Write as _;
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::time::{Duration, Instant};

use eukhe_types::daemon::DaemonCommand;

/// A one-pixel PNG (the clipboard seam fixture image).
const MINIMAL_PNG: &[u8] = &[
    137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73, 72, 68, 82, 0, 0, 0, 1, 0, 0, 0, 1, 8, 6, 0,
    0, 0, 31, 21, 196, 137, 0, 0, 0, 13, 73, 68, 65, 84, 120, 156, 99, 248, 207, 192, 240, 31, 0,
    5, 0, 1, 255, 137, 153, 61, 29, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130,
];

struct Supervisor {
    child: Child,
    socket: PathBuf,
}

/// Stop the daemon on `socket` by protocol so it can shut its workers down;
/// kill the child when the protocol path fails. Drop runs even when the test
/// panics, so a failing test must not leak worker processes.
impl Drop for Supervisor {
    fn drop(&mut self) {
        graceful_shutdown(&self.socket);
        // Snapshot the live worker children before the kill: workers run in
        // their own process groups (detached, TS parity), so a graceful
        // shutdown that times out orphans them when the supervisor dies.
        // Reap them here — the supervisor-lost exit window is a backstop,
        // not the teardown contract.
        let worker_pids = child_pids_of(self.child.id());
        let _ = self.child.kill();
        let _ = self.child.wait();
        for pid in worker_pids {
            kill_worker(pid);
        }
        let _ = std::fs::remove_file(&self.socket);
    }
}

/// Kill a leaked worker process (SIGKILL; it already failed the graceful
/// path) and wait briefly for it to disappear.
fn kill_worker(pid: u32) {
    // The worker pid is a child of the supervisor we just killed, so it is
    // not our child and cannot be waited on directly; poll /proc liveness.
    // Best effort by design: this runs inside `Drop` (a failing test's
    // unwind path included), where an assert would abort the process and
    // orphan every other parallel test's daemons. The contractual
    // worker-leak detection lives in `assert_daemon_stops_clean` (a plain
    // test body, where a panic is a proper failure); here a surviving
    // worker is re-killed and reported to stderr instead.
    for round in 0..2 {
        unsafe {
            libc::kill(pid as i32, libc::SIGKILL);
        }
        let deadline = Instant::now() + Duration::from_secs(5);
        while process_alive(pid) {
            if Instant::now() >= deadline {
                break;
            }
            std::thread::sleep(Duration::from_millis(20));
        }
        if !process_alive(pid) {
            return;
        }
        eprintln!("worker {pid} survived teardown kill round {round}; re-killing");
    }
    eprintln!("worker {pid} still alive after two teardown kills");
}

/// RAII guard for a detached supervisor (spawned by
/// `ensure_daemon_running_with`): shuts the daemon down on scope exit.
struct DetachedDaemon {
    socket: PathBuf,
}

impl Drop for DetachedDaemon {
    fn drop(&mut self) {
        // Best effort by design: this runs inside `Drop` (a failing test's
        // unwind path included), where an assert would ABORT the process and
        // orphan every other parallel test's daemons. A supervisor that
        // misses the graceful exit deadline is SIGKILLed by pid instead.
        let supervisor_pid = graceful_shutdown(&self.socket);
        if let Some(pid) = supervisor_pid {
            // Snapshot the supervisor's live worker children before it goes
            // (they are detached, so they survive its death), then reap any
            // that the graceful shutdown did not stop.
            let worker_pids = child_pids_of(pid);
            let deadline = Instant::now() + Duration::from_secs(10);
            while process_alive(pid) {
                if Instant::now() >= deadline {
                    eprintln!("spawned supervisor {pid} missed the shutdown deadline; killing");
                    unsafe {
                        libc::kill(pid as i32, libc::SIGKILL);
                    }
                    break;
                }
                std::thread::sleep(Duration::from_millis(20));
            }
            for worker in worker_pids {
                kill_worker(worker);
            }
        }
        let _ = std::fs::remove_file(&self.socket);
    }
}

/// Pids whose parent is `ppid` (the supervisor's live worker children).
fn child_pids_of(ppid: u32) -> Vec<u32> {
    let mut pids = Vec::new();
    let entries = std::fs::read_dir("/proc").expect("read /proc");
    for entry in entries.flatten() {
        let Ok(entry_pid) = entry.file_name().to_string_lossy().parse::<u32>() else {
            continue;
        };
        let Ok(stat) = std::fs::read_to_string(format!("/proc/{entry_pid}/stat")) else {
            continue;
        };
        // `comm` can contain spaces and parens, so parse after the last ')'.
        let Some((_, rest)) = stat.rsplit_once(')') else {
            continue;
        };
        let mut fields = rest.split_whitespace();
        fields.next(); // process state
        let Ok(parent) = fields.next().unwrap_or_default().parse::<u32>() else {
            continue;
        };
        if parent == ppid {
            pids.push(entry_pid);
        }
    }
    pids
}

/// Liveness that ignores zombies: a detached child nobody reaps keeps its
/// `/proc` entry (exit status pending), so path existence alone would call
/// an exited process alive.
fn process_alive(pid: u32) -> bool {
    let Ok(stat) = std::fs::read_to_string(format!("/proc/{pid}/stat")) else {
        return false;
    };
    // `comm` can contain spaces and parens, so parse after the last ')'.
    let Some((_, rest)) = stat.rsplit_once(')') else {
        return false;
    };
    let state = rest.split_whitespace().next().unwrap_or_default();
    !state.starts_with('Z') && !state.starts_with('X')
}

/// Shut the spawned supervisor down by protocol and assert that it — and
/// every worker process it spawned — actually exited and the socket file
/// went away. A daemon that only stops its workers but stays parked on its
/// listening socket would leak both processes (the TS client's
/// `waitForDaemonGone` relies on the daemon exiting).
fn assert_daemon_stops_clean(socket: &Path) {
    // Sync JSONL exchange (called from the sync guard path).
    use std::io::{BufRead, BufReader, Write};
    use std::os::unix::net::UnixStream;

    let stream = UnixStream::connect(socket).expect("connect the spawned daemon");
    let write_half = stream.try_clone().expect("clone socket");
    let mut reader = BufReader::new(stream);
    let mut writer = write_half;
    let mut hello = String::new();
    reader.read_line(&mut hello).expect("read daemon_hello");
    let hello: serde_json::Value = serde_json::from_str(hello.trim()).expect("parse hello");
    let supervisor_pid = hello["supervisorPid"].as_u64().expect("supervisorPid") as u32;
    // The worker processes the supervisor spawned for live sessions, captured
    // before the shutdown so reparented workers can still be tracked.
    let worker_pids = child_pids_of(supervisor_pid);

    let command = serde_json::json!({
        "type": "command",
        "id": "stop-assert",
        "protocol": { "name": "eukhe.daemon", "version": 7 },
        "command": { "type": "shutdown" },
    });
    let mut line = serde_json::to_string(&command).expect("serialize");
    line.push('\n');
    writer.write_all(line.as_bytes()).expect("send shutdown");
    writer.flush().expect("flush");

    // The supervisor process exits by itself and cleans up its socket.
    let deadline = Instant::now() + Duration::from_secs(10);
    while process_alive(supervisor_pid) {
        assert!(
            Instant::now() < deadline,
            "the spawned supervisor {supervisor_pid} did not exit after shutdown"
        );
        std::thread::sleep(Duration::from_millis(50));
    }
    assert!(
        !socket.exists(),
        "the spawned supervisor removed its socket file"
    );
    // No worker process outlives the shutdown.
    for pid in worker_pids {
        let deadline = Instant::now() + Duration::from_secs(10);
        while process_alive(pid) {
            assert!(
                Instant::now() < deadline,
                "worker {pid} leaked after shutdown"
            );
            std::thread::sleep(Duration::from_millis(50));
        }
    }
}

/// Sync JSONL shutdown request (Drop runs inside the async test runtime, so
/// no nested runtime may be built here). Best effort; callers kill the child
/// process afterwards regardless. Returns the supervisor pid from the hello
/// so the caller can reap the workers it spawned.
fn graceful_shutdown(socket: &Path) -> Option<u32> {
    use std::io::{BufRead, BufReader, Write};
    use std::os::unix::net::UnixStream;

    let Ok(stream) = UnixStream::connect(socket) else {
        return None;
    };
    let Ok(write_half) = stream.try_clone() else {
        return None;
    };
    let mut reader = BufReader::new(stream);
    let mut writer = write_half;
    let mut hello = String::new();
    let _ = reader.read_line(&mut hello); // daemon_hello
    let supervisor_pid = serde_json::from_str::<serde_json::Value>(hello.trim())
        .ok()
        .and_then(|hello| hello["supervisorPid"].as_u64())
        .map(|pid| pid as u32);

    let command = serde_json::json!({
        "type": "command",
        "id": "test-shutdown",
        "protocol": { "name": "eukhe.daemon", "version": 7 },
        "command": { "type": "shutdown" },
    });
    let Ok(mut line) = serde_json::to_string(&command) else {
        return None;
    };
    line.push('\n');
    if writer.write_all(line.as_bytes()).is_err() {
        return None;
    }
    let _ = writer.flush();
    // Wait briefly for the supervisor to accept the shutdown (it stops every
    // worker before exiting, so the response is the sync point).
    let _ = reader
        .get_ref()
        .set_read_timeout(Some(Duration::from_secs(5)));
    let mut response = String::new();
    let _ = reader.read_line(&mut response);
    supervisor_pid
}

/// The headless run's wall: the plan's barriers are each bounded, but the
/// run loop has no global exit bound — a turn that never settles holds the
/// idle gate closed and the run parks forever. The wall turns that into a
/// failing test instead of a hung binary; dropping the expired future
/// cancels the run loop, and the supervisor guards still tear the daemons
/// down. Generous against real load: the suite settles in 16-63s wall and
/// the longest plan's barriers sum to ~120s.
const HEADLESS_RUN_BOUND: Duration = Duration::from_secs(300);

async fn run_headless_bounded(
    options: eukhe_tui::interactive::InteractiveOptions,
    plan: eukhe_tui::interactive::HeadlessPlan,
) -> anyhow::Result<eukhe_tui::interactive::InteractiveOutcome> {
    let started = Instant::now();
    match tokio::time::timeout(
        HEADLESS_RUN_BOUND,
        eukhe_tui::interactive::run_interactive(options, eukhe_tui::interactive::UiMode::Headless(plan)),
    )
    .await
    {
        Ok(outcome) => outcome,
        Err(tokio::time::error::Elapsed { .. }) => panic!(
            "the headless run exceeded the {HEADLESS_RUN_BOUND:?} wall after {:?}: the wedge class - a turn never settled and the idle gate never opened",
            started.elapsed()
        ),
    }
}

/// Kill supervisors leaked by earlier runs of this verifier: a binary
/// that dies without unwinding (a kill, an abort) runs no `Drop`, so its
/// daemons get reparented to init and keep contending for CPU and memory
/// with every later run. A daemon matches when its `--daemon-socket` sits
/// in a `tempfile`-created `.tmpXXXXXX` dir (this suite's spawn shape —
/// the product's own daemons never use that prefix) and its parent is
/// dead (ppid 1). A daemon of a still-running test keeps its test binary
/// as the parent and never matches.
fn sweep_orphan_test_daemons() {
    static SWEEPED: std::sync::OnceLock<()> = std::sync::OnceLock::new();
    if SWEEPED.set(()).is_err() {
        return; // a later test's spawn: the first spawn already swept
    }
    let mut swept = 0;
    for entry in std::fs::read_dir("/proc").expect("read /proc").flatten() {
        let Ok(pid) = entry.file_name().to_string_lossy().parse::<u32>() else {
            continue;
        };
        let Ok(cmdline) = std::fs::read(format!("/proc/{pid}/cmdline")) else {
            continue;
        };
        // /proc cmdline is NUL-separated.
        let args: Vec<String> = cmdline
            .split(|b| *b == 0)
            .map(|b| String::from_utf8_lossy(b).into_owned())
            .collect();
        let flag = |needle: &str| args.iter().any(|a| a == needle);
        let arg_after = |needle: &str| {
            args.iter()
                .position(|a| a == needle)
                .and_then(|idx| args.get(idx + 1))
                .cloned()
        };
        if !flag("--mode") || arg_after("--mode").as_deref() != Some("daemon") {
            continue;
        }
        let Some(socket) = arg_after("--daemon-socket") else {
            continue;
        };
        // The orphan signature: a test-spawned daemon (its socket lives in a
        // `tempfile`-created `.tmpXXXXXX` dir — the product's own daemons
        // never use that prefix) whose parent is dead (ppid 1 after the
        // killed run's reparent). A live run's daemon keeps its owning test
        // binary as the parent, and the user's product daemons fail the
        // path test, so neither is ever swept.
        let orphan_socket_dir = Path::new(&socket)
            .parent()
            .and_then(Path::file_name)
            .and_then(|name| name.to_str())
            .is_some_and(|name| name.starts_with(".tmp"));
        if !orphan_socket_dir {
            continue;
        }
        let Ok(stat) = std::fs::read_to_string(format!("/proc/{pid}/stat")) else {
            continue;
        };
        let Some((_, rest)) = stat.rsplit_once(')') else {
            continue;
        };
        let Ok(parsed_ppid) = rest
            .split_whitespace()
            .nth(1)
            .unwrap_or_default()
            .parse::<u32>()
        else {
            continue;
        };
        if parsed_ppid != 1 && process_alive(parsed_ppid) {
            continue; // a live run's daemon: its test binary is still up
        }
        unsafe {
            libc::kill(pid as i32, libc::SIGKILL);
        }
        swept += 1;
    }
    if swept > 0 {
        eprintln!("swept {swept} orphan test daemon(s) (socket dir gone) before spawning");
    }
}

#[allow(clippy::zombie_processes)]
fn spawn_supervisor(dir: &Path) -> Supervisor {
    sweep_orphan_test_daemons();
    let socket = dir.join("daemon.sock");
    let agent_dir = dir.join("agent");
    std::fs::create_dir_all(&agent_dir).expect("agent dir");
    let mut command = Command::new(env!("CARGO_BIN_EXE_eukhe"));
    command
        .args(["--mode", "daemon", "--daemon-socket"])
        .arg(&socket)
        .env("EUKHE_CODING_AGENT_DIR", &agent_dir)
        // The daemon's startup catalog refresh must never reach the network
        // from a test: EUKHE_OFFLINE keeps it on the bundled/models.json
        // snapshot (the same fallback the picker renders).
        .env("EUKHE_OFFLINE", "1")
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null());
    // The launcher strips inherited worker role env vars before spawning the
    // supervisor; a CLI running inside a daemon worker must not leak them.
    for var in [
        eukhe_daemon::worker::WORKER_ROLE_ENV,
        eukhe_daemon::worker::WORKER_TOKEN_ENV,
        eukhe_daemon::worker::WORKER_ACTIVE_SESSION_ID_ENV,
        eukhe_daemon::worker::WORKER_RECOVERY_JOURNAL_ENV,
        eukhe_daemon::worker::WORKER_SUPERVISOR_SOCKET_ENV,
        eukhe_daemon::worker::WORKER_SOCKET_ENV,
        eukhe_daemon::worker::WORKER_INSTANCE_ID_ENV,
        eukhe_daemon::worker::WORKER_SCRIPT_ENV,
    ] {
        command.env_remove(var);
    }
    // Ambient provider credentials (PRIME_API_KEY on the dev box, or any
    // other provider key variable) must not leak into the daemon's catalog:
    // every spawned supervisor in this verifier serves fixtures whose only
    // configured model comes from a models.json file, so the ambient
    // catalog cannot widen a test's scope. The supervisor strips these from
    // the session workers it spawns too (they inherit its environment).
    for provider in eukhe_ai::models_generated::get_providers() {
        if let Some(vars) = eukhe_ai::env_api_keys::get_api_key_env_vars(provider) {
            for var in vars {
                command.env_remove(var);
            }
        }
    }
    command.env_remove("PRIME_TEAM_ID");
    // A supervisor killed by a failing test must not leak its session
    // workers into later test binaries: the worker's supervisor-lost exit
    // (TS `exitIfSupervisorOrphanedForTooLong`) runs on this short window
    // instead of the 5-minute default.
    command.env(
        eukhe_daemon::worker::WORKER_SUPERVISOR_LOST_EXIT_MS_ENV,
        "15000",
    );
    // A full workspace run around this suite (the battery) can starve a
    // freshly-launched session worker's boot far past the 30s default
    // connect budget; the generous override keeps the suite's session
    // creates deterministic under that load (the supervisor passes its
    // environment to the workers it spawns).
    command.env("EUKHE_DAEMON_WORKER_CONNECT_TIMEOUT_MS", "90000");
    // Die with this test binary: a supervisor that outlives the process
    // (a kill or abort runs no `Drop`) gets reparented to init and keeps
    // running, so the kernel SIGKILLs it the moment its parent dies. The
    // guard's protocol teardown below stays the normal exit path; this is
    // the backstop. The per-test guards drop before the owning harness
    // thread can exit, so the early-fire window is empty.
    unsafe {
        command.pre_exec(move || {
            libc::prctl(libc::PR_SET_PDEATHSIG, libc::SIGKILL);
            Ok(())
        });
    }
    let child = command.spawn().expect("spawn eukhe --mode daemon");
    let deadline = Instant::now() + Duration::from_mins(1);
    while Instant::now() < deadline {
        if socket.exists() {
            return Supervisor { child, socket };
        }
        std::thread::sleep(Duration::from_millis(20));
    }
    panic!("supervisor socket never appeared");
}

/// Create a live session through the daemon protocol (the same `create`
/// config the TUI sends), writing the scripted engine config first.
async fn create_session_via_daemon(
    socket: &Path,
    script_path: &Path,
    script: &serde_json::Value,
    cwd: &Path,
    session_dir: &Path,
) -> String {
    std::fs::write(script_path, script.to_string()).expect("write script");
    let (client, _events) = eukhe_tui::daemon_client::DaemonClient::connect(socket)
        .await
        .expect("connect supervisor");
    let data = client
        .request_ok(DaemonCommand::Create {
            id: None,
            session_path: None,
            continue_recent: None,
            no_session: None,
            name: None,
            config: Some(serde_json::json!({
                "cwd": cwd.display().to_string(),
                "sessionDir": session_dir.display().to_string(),
                "script": script_path.display().to_string(),
            })),
            telemetry_disabled: None,
            runtime_metadata: None,
            lifecycle: None,
            env: None,
            launch_env: None,
            rest: serde_json::Map::default(),
        })
        .await
        .expect("create session");
    client.close();
    data.get("activeSessionId")
        .or_else(|| data.get("id"))
        .and_then(serde_json::Value::as_str)
        .expect("session id")
        .to_string()
}

/// The base options every utility-command verifier shares.
fn base_options(
    supervisor: &Supervisor,
    dir: &Path,
    session_dir: &Path,
) -> eukhe_tui::interactive::InteractiveOptions {
    eukhe_tui::interactive::InteractiveOptions {
        models: None,
        socket_path: supervisor.socket.clone(),
        cwd: dir.to_path_buf(),
        session_dir: Some(session_dir.to_path_buf()),
        script_path: Some(dir.join("script.json")),
        model_selection: eukhe_tui::interactive::ModelSelection::default(),
        model_catalog: Vec::new(),
        model_configured_providers: std::collections::HashSet::default(),
        model_recent_models: Vec::new(),
        default_thinking_level: None,
        no_session: false,
        session: eukhe_tui::interactive::SessionSelection::New,
        show_images: true,
        screen_mode: eukhe_tui::screen_mode::ScreenMode::Inline,
        initial_message: None,
        theme: "eukhe".to_string(),
        code_block_indent: "  ".to_string(),
        tree_filter_mode: String::new(),
        branch_summary_skip_prompt: false,
        version: "0.0.0".to_string(),
        onboarding: None,
        telemetry_disabled: None,
        client_auth: None,
        telemetry: None,
        keybindings: eukhe_tui::keybindings::KeybindingsManager::new(),
        session_rlm_depth: None,
        prompt_stash: std::sync::Arc::default(),
        session_has_children: false,
        restore_dock_focus: false,
        client_settings: None,
        provider_auth: None,
        traces: None,
    }
}

mod commands;
mod onboarding;
mod panes;
mod rendering;
mod sessions;
mod stash;
