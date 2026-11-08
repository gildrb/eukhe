//! Headless parity (REPORT.md, finish drill): the real binary, an isolated
//! HOME, and the scripted faux provider (`EUKHE_FAUX_SCRIPT`). A `bash`
//! script outlives the blocking budget (500 ms here) and detaches; the
//! model ends its turn promising to report. The settled job wakes the
//! session into another turn in print mode (which exits only once the
//! session is quiescent) and in RPC mode; and a run that ends as
//! `model_error` exits non-zero in both print output modes.

use std::io::{BufRead, BufReader, Write};
use std::path::Path;
use std::process::Stdio;
use std::sync::mpsc::{channel, RecvTimeoutError};
use std::time::{Duration, Instant};

use serde_json::{json, Value};

#[path = "support/eukhe.rs"]
mod eukhe;
use eukhe::eukhe_command;

const PROMISE: &str = "The build is running in the background; I'll report when its job settles.";
const WOKEN: &str = "WOKEN: the build job settled; marker written.";

/// The drill's scenario on a short budget: start a 3 s script, end the
/// turn, answer [`WOKEN`] only if woken.
fn wake_script() -> Value {
    json!({ "responses": [
        { "content": [{ "type": "toolCall", "name": "bash", "id": "call-1",
            "arguments": { "script": "sleep 3; echo WAKE-MARKER > marker.txt; echo built" } }],
          "stopReason": "toolUse" },
        { "content": [{ "type": "text", "text": PROMISE }], "stopReason": "stop" },
        { "content": [{ "type": "text", "text": WOKEN }], "stopReason": "stop" },
    ] })
}

/// An isolated home whose agent dir runs `bash` calls on a 500 ms
/// blocking budget.
fn home_with_short_budget() -> tempfile::TempDir {
    let home = tempfile::TempDir::new().unwrap();
    let agent = home.path().join("agent");
    std::fs::create_dir_all(&agent).unwrap();
    std::fs::write(
        agent.join("settings.json"),
        json!({ "toolBlockingBudgetMs": 500 }).to_string(),
    )
    .unwrap();
    home
}

fn print_command(home: &Path, args: &[&str], script: &Value) -> std::process::Command {
    let mut command = eukhe_command();
    command
        .args(args)
        .env("HOME", home)
        .env("EUKHE_CODING_AGENT_DIR", home.join("agent"))
        .env("EUKHE_DAEMON_SOCKET", home.join("daemon.sock"))
        .env("EUKHE_FAUX_SCRIPT", script.to_string())
        .env("EUKHE_OFFLINE", "1")
        .env_remove("EUKHE_SESSION_DIR")
        .env_remove("EUKHE_CODING_AGENT_SESSION_DIR")
        .env_remove("RLM_DEPTH")
        .current_dir(home);
    command
}

/// The assistant texts of the json stream's `message_end` events, in order.
fn assistant_texts(events: &[Value]) -> Vec<String> {
    events
        .iter()
        .filter(|event| event["type"] == "message_end" && event["message"]["role"] == "assistant")
        .filter_map(|event| {
            event["message"]["content"]
                .as_array()
                .and_then(|blocks| blocks.iter().find(|block| block["type"] == "text"))
                .and_then(|block| block["text"].as_str())
                .map(str::to_owned)
        })
        .collect()
}

/// Print mode: before, the process exited at the promise and killed the
/// job (no marker, no wake). Now the settled job wakes the session, the
/// woken turn answers, and only then does the process exit 0.
#[test]
fn print_mode_waits_for_the_job_and_runs_the_woken_turn() {
    let home = home_with_short_budget();
    let output = print_command(
        home.path(),
        &[
            "--mode",
            "json",
            "-p",
            "Run the build and tell me when it is done.",
        ],
        &wake_script(),
    )
    .output()
    .expect("binary present");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(0), "stderr: {stderr}");
    let events: Vec<Value> = stdout
        .lines()
        .map(serde_json::from_str)
        .collect::<Result<_, _>>()
        .unwrap();
    assert_eq!(
        assistant_texts(&events),
        vec![PROMISE.to_owned(), WOKEN.to_owned()]
    );
    assert!(
        events.iter().any(|event| event["type"] == "message_end"
            && event["message"]["customType"] == "job_settled"),
        "the settled job's notice reached the session"
    );
    assert_eq!(
        std::fs::read_to_string(home.path().join("marker.txt")).unwrap(),
        "WAKE-MARKER\n"
    );
}

/// The give-up: a job that outlives `--wait-limit-ms` ends the wait with
/// exit 1 and a stderr line naming it.
#[test]
fn print_mode_gives_up_at_the_wait_limit() {
    let home = home_with_short_budget();
    let script = json!({ "responses": [
        { "content": [{ "type": "toolCall", "name": "bash", "id": "call-1",
            "arguments": { "script": "sleep 30" } }],
          "stopReason": "toolUse" },
        { "content": [{ "type": "text", "text": PROMISE }], "stopReason": "stop" },
    ] });
    let output = print_command(
        home.path(),
        &["--wait-limit-ms", "1500", "-p", "Run the build."],
        &script,
    )
    .output()
    .expect("binary present");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "stderr: {stderr}");
    assert!(
        stderr.contains("stopped waiting after 1500 ms") && stderr.contains("job "),
        "stderr: {stderr}"
    );
}

/// A reply of only thinking, again and again: the run fails as
/// `model_error`. Before, json mode exited 0 with an empty stderr (it
/// never derived its exit code).
#[test]
fn a_model_error_run_exits_non_zero_in_both_modes() {
    let thinking = json!({
        "content": [{ "type": "thinking", "thinking": "Let me think about the files first." }],
        "stopReason": "stop"
    });
    let script = json!({ "responses": vec![thinking; 9] });
    for args in [
        &["--mode", "json", "-p", "plan it"][..],
        &["-p", "plan it"][..],
    ] {
        let home = tempfile::TempDir::new().unwrap();
        let output = print_command(home.path(), args, &script)
            .output()
            .expect("binary present");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(output.status.code(), Some(1), "{args:?} stderr: {stderr}");
        // The run's failure text reaches stderr once in both modes.
        assert_eq!(
            stderr.matches("The model gave no answer").count(),
            1,
            "{args:?} stderr: {stderr}"
        );
    }
}

/// RPC mode: before, the job finished but nothing woke the session. Now
/// the settled job starts the woken turn on the open connection.
#[test]
fn rpc_mode_wakes_on_the_settled_job() {
    let home = home_with_short_budget();
    let mut child = print_command(home.path(), &["--mode", "rpc"], &wake_script())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .expect("binary present");
    let mut stdin = child.stdin.take().expect("stdin piped");
    let stdout = child.stdout.take().expect("stdout piped");
    let (tx, lines) = channel();
    std::thread::spawn(move || {
        for line in BufReader::new(stdout).lines().map_while(Result::ok) {
            if tx.send(line).is_err() {
                return;
            }
        }
    });
    let prompt = json!({ "id": "p1", "type": "prompt", "message": "Run the build and tell me when it is done." });
    writeln!(stdin, "{prompt}").unwrap();
    stdin.flush().unwrap();
    let deadline = Instant::now() + Duration::from_secs(90);
    let mut events = Vec::new();
    while !assistant_texts(&events).contains(&WOKEN.to_owned()) {
        let left = deadline.saturating_duration_since(Instant::now());
        match lines.recv_timeout(left) {
            Ok(line) => events.push(serde_json::from_str::<Value>(&line).expect("a JSON line")),
            Err(RecvTimeoutError::Timeout) => {
                panic!("no woken turn: {:?}", assistant_texts(&events))
            }
            Err(RecvTimeoutError::Disconnected) => panic!("rpc stdout closed: {events:?}"),
        }
    }
    assert_eq!(
        assistant_texts(&events),
        vec![PROMISE.to_owned(), WOKEN.to_owned()]
    );
    drop(stdin);
    assert!(child.wait().expect("rpc exit").success());
}
