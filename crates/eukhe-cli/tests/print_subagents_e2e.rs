//! Subagents of a headless `--mode json -p` run: the scripted parent spawns
//! a child from its kernel and ends its turn; the run starts a sandboxed
//! daemon supervisor on demand (the isolated `EUKHE_DAEMON_SOCKET`), the
//! child runs there on its own script (`EUKHE_FAUX_CHILD_SCRIPT`), its
//! report comes back into the parent conversation and wakes it, and the
//! parent's next scripted turn answers before the process exits.

use std::path::{Path, PathBuf};
use std::process::Stdio;
use std::time::Duration;

use serde_json::{json, Value};

#[path = "support/eukhe.rs"]
mod eukhe;
use eukhe::eukhe_command;

/// Stops the supervisor the run started on demand (the product leaves a
/// shared daemon running; a test owns its sandbox) when the test ends,
/// passing or not.
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
    let output = eukhe_command()
        .args(["--mode", "json", "-p", "spawn the kid"])
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
        .current_dir(home)
        .stdin(Stdio::null())
        .output()
        .expect("binary present");
    (
        String::from_utf8_lossy(&output.stdout).to_string(),
        String::from_utf8_lossy(&output.stderr).to_string(),
        output.status.code().unwrap_or(-1),
    )
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
    let child_script = home.path().join("child-script.json");
    std::fs::write(
        &child_script,
        json!({ "responses": [{ "text": "kid report: lane done" }] }).to_string(),
    )
    .unwrap();
    let spawn_cell = "handle = await rlm.spawn(\"run the lane task\", name=\"kid\", why=\"isolate\")\nprint(handle.rlm_child_id)";
    let script = json!({
        "responses": [
            { "content": [
                { "type": "toolCall", "name": "ipython", "arguments": { "code": spawn_cell } },
            ] },
            { "text": "spawn turn done" },
            { "text": "report seen" },
        ],
    });

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
