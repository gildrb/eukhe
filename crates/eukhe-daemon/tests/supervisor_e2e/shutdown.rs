//! The supervisor process-exit paths - the shutdown command and the SIGTERM
//! graceful drain.

use super::process_table::{child_pids_of, process_alive};
use super::*;

/// Wait for the child to exit by itself within `timeout` (no kill).
fn wait_child_exit(child: &mut Child, timeout: Duration) -> Option<std::process::ExitStatus> {
    let deadline = Instant::now() + timeout;
    loop {
        if let Some(status) = child.try_wait().expect("try_wait") {
            return Some(status);
        }
        if Instant::now() > deadline {
            return None;
        }
        std::thread::sleep(Duration::from_millis(50));
    }
}

/// Off Linux the exit keeps its socket file: a refused connect cannot
/// prove the listener closed (a full backlog refuses too), so the file
/// waits for the next start's stale-socket prepare. Both halves hold: the
/// file outlives the exit and serves nothing, and a fresh supervisor on
/// the same path replaces it (a new inode) and serves its hello.
#[cfg(not(target_os = "linux"))]
fn assert_the_next_start_reclaims_the_socket(
    socket: &std::path::Path,
    agent_dir: &std::path::Path,
) {
    use std::os::unix::fs::MetadataExt;
    let stale = std::fs::metadata(socket)
        .expect("the exit leaves its socket file")
        .ino();
    assert!(
        UnixStream::connect(socket).is_err(),
        "nothing serves the left-behind socket file"
    );
    let _successor = spawn_daemon(socket, agent_dir);
    let (_client, hello) = Client::connect(socket);
    assert_eq!(hello["type"], "daemon_hello");
    assert_ne!(
        std::fs::metadata(socket)
            .expect("the successor's socket file")
            .ino(),
        stale,
        "the successor bound a fresh socket file in place of the stale one"
    );
}

/// The shutdown command must stop every worker and exit the supervisor
/// process itself, cleaning up its socket (the CLI's stale-replacement and
/// shutdown paths wait for the daemon to be gone; a supervisor that stays
/// parked on its listening socket would block replacement forever and leak
/// both processes).
#[test]
fn shutdown_command_exits_the_supervisor_process() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let socket = dir.path().join("daemon.sock");
    let agent_dir = dir.path().join("agent");
    std::fs::create_dir_all(agent_dir.join("sessions")).expect("sessions dir");
    let mut daemon = spawn_daemon(&socket, &agent_dir);
    let supervisor_pid = daemon.child.id();
    let (mut client, _hello) = Client::connect(&socket);

    // A live session so a worker process exists when shutdown arrives.
    let script_path = dir.path().join("script.json");
    std::fs::write(
        &script_path,
        serde_json::json!({ "responses": [ { "text": "x" } ] }).to_string(),
    )
    .expect("write script");
    client.send_command(
        "c1",
        &serde_json::json!({
            "type": "create",
            "config": {
                "cwd": dir.path().to_string_lossy(),
                "sessionDir": agent_dir.join("sessions").to_string_lossy(),
                "script": script_path.to_string_lossy(),
            },
        }),
    );
    let created = client.read_response("c1");
    assert_eq!(created["success"], true, "create failed: {created}");
    // The supervisor spawned exactly one worker child for the session.
    let deadline = Instant::now() + Duration::from_secs(10);
    let worker_pids = loop {
        let children = child_pids_of(supervisor_pid);
        if !children.is_empty() {
            break children;
        }
        assert!(Instant::now() < deadline, "worker never spawned");
        std::thread::sleep(Duration::from_millis(50));
    };
    assert_eq!(worker_pids.len(), 1, "one worker per session");

    client.send_command("sd", &serde_json::json!({ "type": "shutdown" }));
    let shutdown = client.read_response("sd");
    assert_eq!(shutdown["success"], true, "shutdown failed: {shutdown}");

    // The supervisor exits on its own, cleanly, and takes the socket file.
    let exit = wait_child_exit(&mut daemon.child, Duration::from_secs(10))
        .expect("the supervisor process exited after shutdown");
    assert!(exit.success(), "supervisor exit: {exit:?}");
    // Linux removes the socket file at the exit; off Linux the exit keeps
    // it and the next start reclaims it (checked once the workers are gone).
    #[cfg(target_os = "linux")]
    assert!(!socket.exists(), "the socket file is removed on exit");

    // No worker process outlives the shutdown.
    let deadline = Instant::now() + Duration::from_secs(10);
    for pid in worker_pids {
        while process_alive(pid) {
            assert!(
                Instant::now() < deadline,
                "worker {pid} leaked after shutdown"
            );
            std::thread::sleep(Duration::from_millis(50));
        }
    }
    #[cfg(not(target_os = "linux"))]
    assert_the_next_start_reclaims_the_socket(&socket, &agent_dir);
}

/// The OS-signal drain, end to end: a SIGTERM to the live supervisor is
/// the graceful drain, not the default signal death - the process exits 0
/// (a signal kill reports no exit code) and cleans its socket file up
/// behind it. A connected client rides the drain; the in-crate
/// supervisor tests hold the closing/settle semantics.
#[test]
fn a_sigterm_exits_the_supervisor_through_the_graceful_drain() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let socket = dir.path().join("daemon.sock");
    let agent_dir = dir.path().join("agent");
    std::fs::create_dir_all(&agent_dir).expect("agent dir");
    let mut daemon = spawn_daemon(&socket, &agent_dir);
    let (_client, hello) = Client::connect(&socket);
    assert_eq!(hello["type"], "daemon_hello");
    let _ = Command::new("kill")
        .arg("-TERM")
        .arg(daemon.child.id().to_string())
        .status()
        .expect("SIGTERM the supervisor");
    let deadline = Instant::now() + Duration::from_secs(10);
    let status = loop {
        if let Ok(Some(status)) = daemon.child.try_wait() {
            break status;
        }
        assert!(
            Instant::now() < deadline,
            "the drained supervisor must exit"
        );
        std::thread::sleep(Duration::from_millis(20));
    };
    assert!(
        status.success(),
        "the drain must end in a clean exit 0, not a signal death: {status}"
    );
    // Linux removes the socket file at the exit; off Linux the exit keeps
    // it and the next start reclaims it.
    #[cfg(target_os = "linux")]
    assert!(
        !socket.exists(),
        "the drained supervisor cleans its socket file up"
    );
    #[cfg(not(target_os = "linux"))]
    assert_the_next_start_reclaims_the_socket(&socket, &agent_dir);
}

/// A SIGTERM that lands as soon as the socket first accepts a connect -
/// while the boot still awaits between the bind and the accept loop - is
/// the graceful drain too, never the default signal death. The handlers
/// used to be installed only after the post-bind boot steps (the identity
/// capture, the chat-memory claim), so a stop sent right after a
/// successful readiness connect killed the supervisor outright and
/// stranded its socket file. The bind-capture gap seam parks the boot in
/// that window, so the signal provably lands there; the drain begun
/// before the accept loop makes the loop exit on entry, and the exit
/// cleanup removes the supervisor's own socket file.
#[test]
fn a_sigterm_landing_before_the_accept_loop_still_drains() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let socket = dir.path().join("daemon.sock");
    let agent_dir = dir.path().join("agent");
    std::fs::create_dir_all(&agent_dir).expect("agent dir");
    let mut daemon = Daemon::spawn(
        supervisor_command(&socket, &agent_dir)
            // Wide enough that the SIGTERM below provably lands inside the
            // window (the seam's upper bound).
            .env(eukhe_daemon::socket::BIND_CAPTURE_GAP_ENV, "2000"),
        &socket,
    );
    // The listen backlog accepts the connect while the boot is parked.
    let deadline = Instant::now() + Duration::from_secs(10);
    while UnixStream::connect(&socket).is_err() {
        assert!(
            Instant::now() < deadline,
            "the supervisor socket never accepted a connect"
        );
        std::thread::sleep(Duration::from_millis(10));
    }
    let _ = Command::new("kill")
        .arg("-TERM")
        .arg(daemon.child.id().to_string())
        .status()
        .expect("SIGTERM the supervisor");
    let status = wait_child_exit(&mut daemon.child, Duration::from_secs(15))
        .expect("the drained supervisor must exit");
    assert!(
        status.success(),
        "the early drain must end in a clean exit 0, not a signal death: {status}"
    );
    // Linux removes the socket file at the exit; off Linux the exit keeps
    // it and the next start reclaims it.
    #[cfg(target_os = "linux")]
    assert!(
        !socket.exists(),
        "the drained supervisor cleans its socket file up"
    );
    #[cfg(not(target_os = "linux"))]
    assert_the_next_start_reclaims_the_socket(&socket, &agent_dir);
}
