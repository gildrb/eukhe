//! Subagents of a headless `--mode json -p` run: the scripted parent spawns
//! a child from its kernel and ends its turn; the run starts a sandboxed
//! daemon supervisor on demand (the isolated `EUKHE_DAEMON_SOCKET`), the
//! child runs there on its own script (`EUKHE_FAUX_CHILD_SCRIPT`), its
//! report comes back into the parent conversation and wakes it, and the
//! parent's next scripted turn answers before the process exits. The
//! child messages its headless parent like a daemon parent, and nothing
//! the run started outlives it.

use std::collections::BTreeMap;
use std::io::{BufRead as _, BufReader, Write as _};
use std::path::{Path, PathBuf};
use std::process::Stdio;
use std::time::{Duration, Instant};

use serde_json::{json, Value};

#[path = "support/eukhe.rs"]
mod eukhe;
use eukhe::{daemon_mode_args, eukhe_command};

/// Stops a supervisor left on the sandbox's socket (a run tied to its own
/// supervisor leaves none; a test owns its sandbox either way) when the
/// test ends, passing or not.
struct SandboxedDaemon {
    socket: PathBuf,
}

impl Drop for SandboxedDaemon {
    fn drop(&mut self) {
        use std::io::{BufRead as _, BufReader, Write as _};
        let Ok(mut stream) = eukhe_types::platform::transport::connect_blocking(&self.socket)
        else {
            return;
        };
        let Ok(reader) = stream.try_clone_box() else {
            return;
        };
        let _ = reader.set_read_timeout(Duration::from_secs(30));
        let frame = json!({
            "type": "command",
            "id": "shutdown-test",
            "protocol": { "name": "eukhe.daemon", "version": eukhe_types::daemon::DAEMON_PROTOCOL_VERSION },
            "command": { "type": "shutdown" },
        });
        if writeln!(stream, "{frame}").is_err() || stream.flush().is_err() {
            return;
        }
        // Readiness: the shutdown answer, then the supervisor closes.
        let _ = BufReader::new(reader)
            .lines()
            .map_while(Result::ok)
            .find(|line| line.contains("shutdown-test"));
    }
}

/// The text of every message the json stream ended.
fn ended_messages(stdout: &str) -> Vec<Value> {
    stdout
        .lines()
        .filter_map(|line| serde_json::from_str::<Value>(line).ok())
        .filter(|event| event["type"] == "message_end")
        .map(|event| event["message"].clone())
        .collect()
}

fn run_json(
    home: &Path,
    socket: &Path,
    script: &Value,
    child_script: &Path,
) -> (String, String, i32) {
    let output = headless_command(home, socket, script, child_script)
        .args(["--mode", "json", "-p", "spawn the kid"])
        .stdin(Stdio::null())
        .output()
        .expect("binary present");
    (
        String::from_utf8_lossy(&output.stdout).to_string(),
        String::from_utf8_lossy(&output.stderr).to_string(),
        output.status.code().unwrap_or(-1),
    )
}

/// A headless `eukhe` on the isolated `home` and daemon `socket`, its
/// parent on `script` and every child on `child_script`.
fn headless_command(
    home: &Path,
    socket: &Path,
    script: &Value,
    child_script: &Path,
) -> std::process::Command {
    let mut command = eukhe_command();
    command
        .env("HOME", home)
        .env("EUKHE_DAEMON_SOCKET", socket)
        .env("EUKHE_FAUX_SCRIPT", script.to_string())
        .env("EUKHE_FAUX_CHILD_SCRIPT", child_script)
        .env("EUKHE_OFFLINE", "1")
        // A supervisor the test fails to stop takes its workers down soon.
        .env(
            eukhe_daemon::worker::WORKER_SUPERVISOR_LOST_EXIT_MS_ENV,
            "15000",
        )
        .env_remove("RLM_DEPTH")
        .env("EUKHE_CODING_AGENT_DIR", home.join("agent"))
        .current_dir(home);
    command
}

/// The kernel cell a parent spawns its child with.
const SPAWN_CELL: &str = "handle = await rlm.spawn(\"run the lane task\", name=\"kid\", why=\"isolate\")\nprint(handle.rlm_child_id)";

/// The parent's script: the spawn turn, then a text answer for each turn
/// a report or a message wakes.
fn spawn_script(answers: &[&str]) -> Value {
    let mut responses = vec![
        json!({ "content": [
            { "type": "toolCall", "name": "ipython", "arguments": { "code": SPAWN_CELL } },
        ] }),
        json!({ "text": "spawn turn done" }),
    ];
    responses.extend(answers.iter().map(|text| json!({ "text": text })));
    json!({ "responses": responses })
}

/// Write the children's script into `home`.
fn write_child_script(home: &Path, script: &Value) -> PathBuf {
    let path = home.join("child-script.json");
    std::fs::write(&path, script.to_string()).unwrap();
    path
}

/// The live processes of the sandbox: every process (but this test) whose
/// environment names `home` as its HOME or whose command line names `home`
/// or `socket`, by pid, with its command line.
fn sandbox_processes(home: &Path, socket: &Path) -> BTreeMap<u32, String> {
    let home_entry = format!("HOME={}", home.display());
    let home_text = home.display().to_string();
    let socket_text = socket.display().to_string();
    let mut found = BTreeMap::new();
    for entry in std::fs::read_dir("/proc").expect("procfs").flatten() {
        let Some(pid) = entry
            .file_name()
            .to_str()
            .and_then(|name| name.parse::<u32>().ok())
        else {
            continue;
        };
        if pid == std::process::id() {
            continue;
        }
        // A process that exits during the scan reads as nothing.
        let environ = std::fs::read(entry.path().join("environ")).unwrap_or_default();
        let cmdline = std::fs::read(entry.path().join("cmdline"))
            .unwrap_or_default()
            .split(|byte| *byte == 0)
            .map(String::from_utf8_lossy)
            .collect::<Vec<_>>()
            .join(" ");
        let in_sandbox = environ
            .split(|byte| *byte == 0)
            .any(|var| var == home_entry.as_bytes())
            || cmdline.contains(&home_text)
            || cmdline.contains(&socket_text);
        if in_sandbox {
            found.insert(pid, cmdline);
        }
    }
    found
}

/// Wait (bounded) until the sandbox's live processes are exactly `kept`;
/// returns the processes it ended with.
fn wait_sandbox_processes(home: &Path, socket: &Path, kept: &[u32]) -> BTreeMap<u32, String> {
    let deadline = Instant::now() + Duration::from_secs(60);
    loop {
        let live = sandbox_processes(home, socket);
        if live.keys().copied().eq(kept.iter().copied()) || Instant::now() >= deadline {
            return live;
        }
        std::thread::sleep(Duration::from_millis(100));
    }
}

/// `rlm.spawn` from a headless session creates its child through the
/// daemon supervisor (started on demand), and the child's report wakes
/// the parent: its next scripted turn answers and the run exits 0.
#[test]
fn print_json_spawn_reports_back_and_wakes_the_parent() {
    let home = tempfile::TempDir::new().unwrap();
    let socket = home.path().join("daemon.sock");
    let _daemon = SandboxedDaemon {
        socket: socket.clone(),
    };
    let child_script = write_child_script(
        home.path(),
        &json!({ "responses": [{ "text": "kid report: lane done" }] }),
    );
    let script = spawn_script(&["report seen"]);

    let (stdout, stderr, code) = run_json(home.path(), &socket, &script, &child_script);

    assert_eq!(code, 0, "stdout: {stdout}\nstderr: {stderr}");
    let messages = ended_messages(&stdout);
    let spawn_result = messages
        .iter()
        .find(|message| message["role"] == "toolResult")
        .unwrap_or_else(|| panic!("the spawn cell's result: {stdout}"));
    assert!(
        spawn_result.to_string().contains("sub-"),
        "the spawn returned a child id, not an error: {spawn_result}"
    );
    assert!(
        messages.iter().any(|message| message["role"] != "assistant"
            && message.to_string().contains("kid report: lane done")),
        "the child's report reached the parent conversation: {stdout}"
    );
    let last_answer = messages
        .iter()
        .rev()
        .find(|message| message["role"] == "assistant")
        .unwrap_or_else(|| panic!("an assistant answer: {stdout}"));
    assert_eq!(
        last_answer["content"][0]["text"], "report seen",
        "the report woke the parent's next turn: {stdout}\nstderr: {stderr}"
    );
}

/// The children's script of the messaging runs: the child messages its
/// parent from its kernel, then reports.
fn messaging_child_script() -> Value {
    let send_cell = "import agent_message\nreceipt = await agent_message.send(\"kid says hi\", receiver_role=\"parent\")\nprint(receipt)";
    json!({ "responses": [
        { "content": [
            { "type": "toolCall", "name": "ipython", "arguments": { "code": send_cell } },
        ] },
        { "text": "kid report: message sent" },
    ] })
}

/// A child's `agent_message.send(..., receiver_role="parent")` reaches its
/// headless parent: the message lands in the parent conversation as an
/// agent message, a later parent turn answers, and the run exits 0.
#[test]
fn print_json_child_messages_its_headless_parent() {
    let home = tempfile::TempDir::new().unwrap();
    let socket = home.path().join("daemon.sock");
    let _daemon = SandboxedDaemon {
        socket: socket.clone(),
    };
    let child_script = write_child_script(home.path(), &messaging_child_script());
    let script = spawn_script(&["woken once", "woken twice", "woken thrice"]);

    let (stdout, stderr, code) = run_json(home.path(), &socket, &script, &child_script);

    assert_eq!(code, 0, "stdout: {stdout}\nstderr: {stderr}");
    let messages = ended_messages(&stdout);
    // The child's message, as the agent-message card from the parent's
    // child.
    let delivered = messages
        .iter()
        .position(|message| {
            message["role"] == "custom"
                && message["customType"] == "agent_message"
                && message["details"]["message"] == "kid says hi"
                && message["details"]["fromRelationship"] == "child"
        })
        .unwrap_or_else(|| {
            panic!("the child's message reached the parent: {stdout}\nstderr: {stderr}")
        });
    assert!(
        messages[delivered..]
            .iter()
            .any(|message| message["role"] == "assistant"),
        "a parent turn answered after the message: {stdout}"
    );
    // The message was the child's reply: its exit owes no no-reply notice.
    assert!(
        !stdout.contains("no-reply child:kid"),
        "the child's message counts as its reply: {stdout}"
    );
}

/// When a `-p` run whose child messaged it exits, nothing it started
/// remains: the supervisor it started for its children drained, and the
/// children and their kernels stopped with it.
#[test]
fn print_run_leaves_no_process_behind() {
    let home = tempfile::TempDir::new().unwrap();
    let socket = home.path().join("daemon.sock");
    let _daemon = SandboxedDaemon {
        socket: socket.clone(),
    };
    let child_script = write_child_script(home.path(), &messaging_child_script());
    let script = spawn_script(&["woken once", "woken twice", "woken thrice"]);

    let (stdout, stderr, code) = run_json(home.path(), &socket, &script, &child_script);

    assert_eq!(code, 0, "stdout: {stdout}\nstderr: {stderr}");
    let left = wait_sandbox_processes(home.path(), &socket, &[]);
    assert!(left.is_empty(), "processes outlived the run: {left:#?}");
}

/// An RPC session that spawned a child leaves nothing behind once its
/// client closes stdin.
#[test]
fn rpc_session_leaves_no_process_behind() {
    let home = tempfile::TempDir::new().unwrap();
    let socket = home.path().join("daemon.sock");
    let _daemon = SandboxedDaemon {
        socket: socket.clone(),
    };
    let child_script = write_child_script(
        home.path(),
        &json!({ "responses": [{ "text": "kid report: lane done" }] }),
    );
    let script = spawn_script(&["report seen", "nothing more"]);
    let mut rpc = headless_command(home.path(), &socket, &script, &child_script)
        .args(["--mode", "rpc"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .expect("binary present");
    let mut stdin = rpc.stdin.take().expect("stdin piped");
    let stdout = rpc.stdout.take().expect("stdout piped");
    let (lines_tx, lines) = std::sync::mpsc::channel::<String>();
    std::thread::spawn(move || {
        for line in BufReader::new(stdout).lines().map_while(Result::ok) {
            if lines_tx.send(line).is_err() {
                return;
            }
        }
    });
    let prompt = json!({ "type": "prompt", "message": "spawn the kid", "id": "p1" });
    writeln!(stdin, "{prompt}").unwrap();
    stdin.flush().unwrap();
    // Readiness: the turn the child's report woke ended.
    let deadline = Instant::now() + Duration::from_secs(60);
    let mut seen = Vec::new();
    loop {
        let left = deadline.saturating_duration_since(Instant::now());
        let line = lines
            .recv_timeout(left)
            .unwrap_or_else(|error| panic!("no woken turn ({error}): {seen:#?}"));
        let frame: Value = serde_json::from_str(&line).unwrap_or(Value::String(line));
        let woken = frame["type"] == "agent_end" && frame.to_string().contains("report seen");
        seen.push(frame);
        if woken {
            break;
        }
    }

    drop(stdin);
    let status = rpc.wait().expect("the rpc session exits when stdin closes");

    assert!(status.success(), "the rpc exit: {status}");
    let left = wait_sandbox_processes(home.path(), &socket, &[]);
    assert!(left.is_empty(), "processes outlived the session: {left:#?}");
}

/// A daemon that already listened is the user's: a `-p` run that hosted
/// its children there leaves it running, and stops only the children it
/// spawned.
#[test]
fn print_run_keeps_a_running_daemon_and_stops_its_children() {
    let home = tempfile::TempDir::new().unwrap();
    let socket = home.path().join("daemon.sock");
    let mut daemon = eukhe_command();
    daemon_mode_args(&mut daemon, &socket, &home.path().join("agent"))
        .env("HOME", home.path())
        .env("EUKHE_OFFLINE", "1")
        .current_dir(home.path());
    let mut daemon = daemon.spawn().expect("binary present");
    let sandbox = SandboxedDaemon {
        socket: socket.clone(),
    };
    // Readiness: the daemon accepts connections.
    let deadline = Instant::now() + Duration::from_secs(30);
    while eukhe_types::platform::transport::connect_blocking(&socket).is_err() {
        assert!(Instant::now() < deadline, "the daemon never listened");
        std::thread::sleep(Duration::from_millis(20));
    }
    let child_script = write_child_script(
        home.path(),
        &json!({ "responses": [{ "text": "kid report: lane done" }] }),
    );
    let script = spawn_script(&["report seen"]);

    let (stdout, stderr, code) = run_json(home.path(), &socket, &script, &child_script);

    assert_eq!(code, 0, "stdout: {stdout}\nstderr: {stderr}");
    let left = wait_sandbox_processes(home.path(), &socket, &[daemon.id()]);
    assert_eq!(
        left.keys().copied().collect::<Vec<_>>(),
        vec![daemon.id()],
        "only the user's daemon remains: {left:#?}"
    );
    drop(sandbox);
    daemon.wait().expect("the daemon stops on shutdown");
}
