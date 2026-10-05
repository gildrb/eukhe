//! A supervisor whose binary was replaced while it runs (a rebuilt
//! `target/debug/eukhe`, an in-place upgrade) still launches session
//! workers, and they run the supervisor's own build. The regression: the
//! supervisor spawned `current_exe()`, which Linux reports as
//! `<path> (deleted)` once the file is replaced, so every create - an RLM
//! child's included - failed with `spawn session worker <id>`.

#![cfg(target_os = "linux")]

use std::io::{BufRead, BufReader, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::time::{Duration, Instant};

use serde_json::{json, Value};

struct Supervisor {
    child: Child,
}

impl Drop for Supervisor {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

#[allow(clippy::zombie_processes)]
fn spawn_supervisor(binary: &Path, socket: &Path, agent_dir: &Path) -> Supervisor {
    std::fs::create_dir_all(agent_dir).expect("agent dir");
    let child = Command::new(binary)
        .arg("supervisor")
        .arg("--socket")
        .arg(socket)
        .arg("--agent-dir")
        .arg(agent_dir)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .env_remove("PRIME_API_KEY")
        .env_remove("EUKHE_CODING_AGENT_DIR")
        // A supervisor killed at teardown must not leak its session workers
        // into later test binaries.
        .env(
            eukhe_daemon::worker::WORKER_SUPERVISOR_LOST_EXIT_MS_ENV,
            "15000",
        )
        .spawn()
        .expect("spawn eukhe-daemon supervisor");
    let deadline = Instant::now() + Duration::from_secs(10);
    while Instant::now() < deadline {
        if socket.exists() {
            return Supervisor { child };
        }
        std::thread::sleep(Duration::from_millis(20));
    }
    panic!("supervisor socket never appeared");
}

fn read_line(reader: &mut BufReader<std::os::unix::net::UnixStream>) -> Value {
    let mut line = String::new();
    loop {
        let read = reader.read_line(&mut line).expect("read supervisor line");
        assert_ne!(read, 0, "supervisor closed the connection");
        if !line.trim().is_empty() {
            return serde_json::from_str(line.trim()).expect("parse line");
        }
        line.clear();
    }
}

/// The supervisor's private copy of the daemon binary: a hard link on the
/// target filesystem (a copy when the link cannot be made), so replacing it
/// never touches the cargo-built binary other tests run.
fn private_binary(dir: &Path) -> PathBuf {
    let bin_dir = dir.join("bin");
    std::fs::create_dir_all(&bin_dir).expect("bin dir");
    let binary = bin_dir.join("eukhe-daemon");
    let built = env!("CARGO_BIN_EXE_eukhe-daemon");
    if std::fs::hard_link(built, &binary).is_err() {
        std::fs::copy(built, &binary).expect("copy daemon binary");
    }
    binary
}

#[test]
fn a_replaced_supervisor_binary_still_launches_workers_of_its_own_build() {
    let dir = tempfile::TempDir::new_in(env!("CARGO_TARGET_TMPDIR")).expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("sessions dir");
    let script = dir.path().join("faux.json");
    std::fs::write(
        &script,
        json!({ "engine": "faux", "responses": [{ "text": "scripted reply" }] }).to_string(),
    )
    .expect("write faux script");
    let binary = private_binary(dir.path());
    let socket = dir.path().join("d.sock");
    let _supervisor = spawn_supervisor(&binary, &socket, &agent_dir);

    // Replace the binary under the running supervisor with a different
    // "build": a worker launched from the path would run it (and exit 97).
    std::fs::remove_file(&binary).expect("unlink the supervisor binary");
    std::fs::write(&binary, "#!/bin/sh\nexit 97\n").expect("write the replacement");
    let mut permissions = std::fs::metadata(&binary)
        .expect("replacement metadata")
        .permissions();
    std::os::unix::fs::PermissionsExt::set_mode(&mut permissions, 0o755);
    std::fs::set_permissions(&binary, permissions).expect("make the replacement executable");

    let stream = std::os::unix::net::UnixStream::connect(&socket).expect("connect");
    stream
        .set_read_timeout(Some(Duration::from_mins(2)))
        .expect("read timeout");
    let mut writer = stream.try_clone().expect("clone stream");
    let mut reader = BufReader::new(stream);
    assert_eq!(read_line(&mut reader)["type"], "daemon_hello");
    let envelope = json!({
        "type": "command",
        "id": "c1",
        "protocol": { "name": "eukhe.daemon", "version": 7 },
        "command": {
            "type": "create",
            "config": {
                "cwd": dir.path().to_string_lossy(),
                "sessionDir": session_dir.to_string_lossy(),
                "script": script.to_string_lossy(),
            },
        },
    });
    let mut line = serde_json::to_string(&envelope).expect("serialize");
    line.push('\n');
    writer.write_all(line.as_bytes()).expect("send create");
    let created = loop {
        let line = read_line(&mut reader);
        if line.get("id").and_then(Value::as_str) == Some("c1") {
            break line;
        }
    };
    assert_eq!(created["success"], true, "create failed: {created}");
}
