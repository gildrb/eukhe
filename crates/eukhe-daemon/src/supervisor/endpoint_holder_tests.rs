//! The stuck-worker oracle: a worker whose stop failed and that still runs
//! keeps its endpoint, on Linux an abstract name the kernel frees only
//! when that process exits. A relaunch stops the holder before it spawns,
//! so the replacement never runs beside it. Linux only: the stop's signals
//! ride the pidfd, which opens only where the kernel provides it.

use super::*;

/// The endpoint the stand-in holder binds, passed in its environment.
const HOLDER_ENDPOINT_ENV: &str = "EUKHE_TEST_ENDPOINT_HOLDER";

/// The file the holder writes once its endpoint is bound.
fn ready_marker(endpoint: &Path) -> PathBuf {
    endpoint.with_extension("ready")
}

/// Kills the holder when the test ends, whatever its outcome.
struct KillOnDrop(std::process::Child);

impl Drop for KillOnDrop {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

/// The stand-in for a worker whose stop failed: run as its own process
/// (this test binary, this test alone), it binds the endpoint its
/// environment names as a worker binds it, recording its pid, marks
/// itself ready, and serves nothing until it is killed. A plain test run,
/// without the environment, passes at once.
#[test]
fn endpoint_holder_process() {
    let Some(endpoint) = std::env::var_os(HOLDER_ENDPOINT_ENV) else {
        return;
    };
    let endpoint = PathBuf::from(endpoint);
    let _listener =
        eukhe_types::platform::transport::bind_std(&endpoint).expect("bind the held endpoint");
    std::fs::write(ready_marker(&endpoint), b"").expect("mark the holder ready");
    loop {
        std::thread::sleep(Duration::from_secs(60));
    }
}

/// A live process still holds the worker's endpoint when its relaunch
/// runs: the relaunch stops it, then spawns. Without the stop the
/// replacement could not bind, its launch probe would reach the old
/// process, and the holder would outlive the relaunch.
#[tokio::test]
async fn a_relaunch_stops_the_live_holder_of_its_endpoint_before_the_spawn() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    std::fs::create_dir_all(&agent_dir).expect("agent dir");
    let supervisor = Arc::new(
        Supervisor::new(SupervisorOptions {
            socket_path: dir.path().join("daemon.sock"),
            agent_dir,
        })
        .expect("supervisor"),
    );
    // No replacement ever answers: the relaunch ends at the launch probe,
    // after the spawn.
    supervisor.pin_worker_connect_budget_for_tests(Duration::from_millis(1));

    let endpoint = dir.path().join("w-held.sock");
    let mut holder = KillOnDrop(
        std::process::Command::new(std::env::current_exe().expect("test binary"))
            .args([
                "--exact",
                "supervisor::endpoint_holder_tests::endpoint_holder_process",
            ])
            .env(HOLDER_ENDPOINT_ENV, &endpoint)
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .spawn()
            .expect("spawn the holder"),
    );
    let deadline = tokio::time::Instant::now() + Duration::from_secs(30);
    while !ready_marker(&endpoint).exists() {
        assert!(
            tokio::time::Instant::now() < deadline,
            "the holder never bound its endpoint"
        );
        tokio::time::sleep(Duration::from_millis(20)).await;
    }
    let holder_pid = holder.0.id();
    assert_eq!(
        eukhe_types::platform::transport::listener_pid(
            &endpoint,
            eukhe_bend::rules::server_peer::PEER_RULES
        )
        .await
        .expect("the client rule accepts the holder"),
        Some(holder_pid),
        "the holder serves the endpoint as its recorded process"
    );

    let descriptor_path = dir.path().join("w-held.json");
    let descriptor: DaemonWorkerDescriptor = serde_json::from_value(serde_json::json!({
        "version": 2,
        "workerId": "w-held",
        "pid": holder_pid,
        "socketPath": endpoint.to_string_lossy(),
        "recoveryJournalPath": dir.path().join("w-held.recovery.jsonl").to_string_lossy(),
        "supervisorSocketPath": dir.path().join("daemon.sock").to_string_lossy(),
        "authenticationToken": "held-token",
        "rootActiveSessionId": "w-held",
        "createdAt": "2026-10-01T00:00:00Z",
        "updatedAt": "2026-10-01T00:00:00Z",
        "lifecycle": "ready",
        // A spawn runs in the session's own cwd, which must exist.
        "createCommand": { "cwd": dir.path().to_string_lossy() },
        "consecutiveFailures": 0,
    }))
    .expect("descriptor");
    let resident = ResidentWorker::new("w-held".to_string(), descriptor, descriptor_path.clone());
    supervisor.registry.insert(Arc::clone(&resident)).await;

    let outcome = supervisor.relaunch_worker(&resident).await;
    assert!(
        outcome.is_err(),
        "no replacement answers: the relaunch fails at the probe"
    );
    assert!(
        holder.0.try_wait().expect("the holder's status").is_some(),
        "the holder of the endpoint outlived the relaunch"
    );
    let spawned: DaemonWorkerDescriptor = serde_json::from_str(
        &std::fs::read_to_string(&descriptor_path).expect("the spawn record is readable"),
    )
    .expect("parse the spawn record");
    assert!(
        spawned.pid > 0 && spawned.pid != u64::from(holder_pid),
        "the replacement spawned once the holder was gone: {}",
        spawned.pid
    );
}
