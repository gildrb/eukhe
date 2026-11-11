//! `jobs.wait`, the agent's one blocking wait (finish drill, REPORT.md
//! root cause 3 and 4): the real binary in print mode, an isolated HOME,
//! the scripted faux provider (`EUKHE_FAUX_SCRIPT`), a real kernel and a
//! 500 ms blocking budget, so a 3 s job outlives the budget six times over
//! as the drill's 45 s job outlived the 30 s one.

use std::path::Path;
use std::process::Command;

use serde_json::{json, Value};

#[path = "support/eukhe.rs"]
mod eukhe;
use eukhe::eukhe_command;

/// An isolated home whose agent dir runs calls on a 500 ms blocking
/// budget, its working tree a fresh git repo (a throwaway repo of the
/// test, so it carries its own identity).
fn home_with_short_budget() -> tempfile::TempDir {
    let home = tempfile::TempDir::new().unwrap();
    let agent = home.path().join("agent");
    std::fs::create_dir_all(&agent).unwrap();
    std::fs::write(
        agent.join("settings.json"),
        json!({ "toolBlockingBudgetMs": 500 }).to_string(),
    )
    .unwrap();
    for args in [
        &["init", "-q", "."][..],
        &["config", "user.name", "jobs-wait-test"],
        &["config", "user.email", "jobs-wait-test@example.invalid"],
    ] {
        let status = Command::new("git")
            .args(args)
            .current_dir(home.path())
            .status()
            .unwrap();
        assert!(status.success(), "git {args:?}");
    }
    home
}

/// Run `script` in print mode (json stream): the exit code and the events.
fn run(home: &Path, script: &Value) -> (Option<i32>, Vec<Value>, String) {
    let output = eukhe_command()
        .args(["--mode", "json", "-p", "Run the build, then commit it."])
        .env("HOME", home)
        .env("EUKHE_CODING_AGENT_DIR", home.join("agent"))
        .env("EUKHE_DAEMON_SOCKET", home.join("daemon.sock"))
        .env("EUKHE_FAUX_SCRIPT", script.to_string())
        .env("EUKHE_OFFLINE", "1")
        .env_remove("EUKHE_SESSION_DIR")
        .env_remove("EUKHE_CODING_AGENT_SESSION_DIR")
        .env_remove("RLM_DEPTH")
        .current_dir(home)
        .output()
        .expect("binary present");
    let events = String::from_utf8_lossy(&output.stdout)
        .lines()
        .map(serde_json::from_str)
        .collect::<Result<Vec<Value>, _>>()
        .unwrap();
    (
        output.status.code(),
        events,
        String::from_utf8_lossy(&output.stderr).into_owned(),
    )
}

fn call(id: &str, name: &str, arguments: &Value) -> Value {
    json!({ "content": [{ "type": "toolCall", "name": name, "id": id, "arguments": arguments }],
            "stopReason": "toolUse" })
}

fn answer(text: &str) -> Value {
    json!({ "content": [{ "type": "text", "text": text }], "stopReason": "stop" })
}

/// The finished messages of `role` (and custom type), as their first text.
fn texts(events: &[Value], role: &str) -> Vec<String> {
    events
        .iter()
        .filter(|event| event["type"] == "message_end" && event["message"]["role"] == role)
        .map(|event| {
            let content = &event["message"]["content"];
            content
                .as_array()
                .and_then(|blocks| blocks.iter().find_map(|block| block["text"].as_str()))
                .or_else(|| content.as_str())
                .unwrap_or_default()
                .to_owned()
        })
        .collect()
}

/// The texts of the `job_settled` notices the run delivered.
fn job_settled_notices(events: &[Value]) -> Vec<String> {
    events
        .iter()
        .filter(|event| {
            event["type"] == "message_end" && event["message"]["customType"] == "job_settled"
        })
        .map(|event| event["message"]["content"].to_string())
        .collect()
}

/// The drill's task C/W shape: the build outlives the budget and detaches;
/// the model waits for it in the same turn with `jobs.wait()`, gets its
/// output, commits, and ends. Before, `jobs.wait` knew only kernel cells
/// (a `bash` tool job was no target), clamped every wait to the budget,
/// and the model's only way to the result was to end its turn.
///
/// Whether the build settles before the wait opens is the scheduler's:
/// the wait's cell first starts the kernel, which takes seconds on a
/// loaded machine. A wait open when the build settles takes its result
/// (no notice); a build that settled first left its result to its notice,
/// so the wait ends on that queued notice, which follows it in the same
/// run. Either way the result reaches the turn once, before the commit.
#[test]
fn a_detached_build_is_waited_for_and_committed_in_one_turn() {
    let home = home_with_short_budget();
    let script = json!({ "responses": [
        call("call-1", "bash", &json!({ "script": "sleep 3; echo built > out.txt; echo BUILD-OK" })),
        call("call-2", "python", &json!({ "code": "job = await jobs.wait()\nprint(job.kind, job.state, job.output.splitlines()[-1])" })),
        call("call-3", "bash", &json!({ "script": "git add out.txt && git commit -q -m build && git log --oneline | wc -l" })),
        answer("Built and committed."),
    ] });
    let (code, events, stderr) = run(home.path(), &script);
    assert_eq!(code, Some(0), "stderr: {stderr}");
    let results = texts(&events, "toolResult");
    assert_eq!(results.len(), 3, "{results:?}");
    let notices = job_settled_notices(&events);
    match results[1].as_str() {
        "shell ok BUILD-OK\n" => assert_eq!(
            notices,
            Vec::<String>::new(),
            "the result the wait returned is not delivered again"
        ),
        "message ok A message arrived for this session; it follows this result.\n" => assert!(
            notices.len() == 1 && notices[0].contains("BUILD-OK"),
            "the build's notice follows the wait: {notices:?}"
        ),
        other => panic!("the wait ends on the build: {other:?} ({results:?})"),
    }
    let run_ends = events
        .iter()
        .filter(|event| event["type"] == "agent_end")
        .count();
    assert_eq!(run_ends, 1, "one run");
    let log = Command::new("git")
        .args(["log", "--format=%s"])
        .current_dir(home.path())
        .output()
        .unwrap();
    assert_eq!(
        String::from_utf8_lossy(&log.stdout),
        "build\n",
        "{results:?}"
    );
    assert_eq!(
        texts(&events, "assistant").last().map(String::as_str),
        Some("Built and committed.")
    );
    assert_eq!(
        std::fs::read_to_string(home.path().join("out.txt")).unwrap(),
        "built\n"
    );
}

/// A detached cell holds the kernel; a cell that only waits runs without
/// it and returns the held cell's output. Before, every python call while
/// a cell was detached answered "Not run: the kernel is still running job".
#[test]
fn a_wait_runs_while_a_detached_cell_holds_the_kernel() {
    let home = home_with_short_budget();
    let script = json!({ "responses": [
        call("call-1", "python", &json!({ "code": "import time\ntime.sleep(3)\nprint('CELL-DONE')" })),
        call("call-2", "python", &json!({ "code": "await jobs.wait()" })),
        answer("The cell finished."),
    ] });
    let (code, events, stderr) = run(home.path(), &script);
    assert_eq!(code, Some(0), "stderr: {stderr}");
    let results = texts(&events, "toolResult");
    assert_eq!(results.len(), 2, "{results:?}");
    assert!(
        results[1].starts_with("[served without the kernel: job cell-")
            && results[1].contains(") ok after ")
            && results[1].ends_with("CELL-DONE\n"),
        "{results:?}"
    );
    assert_eq!(job_settled_notices(&events), Vec::<String>::new());
}

/// With nothing running and nothing ready, the wait is refused at once
/// instead of blocking.
#[test]
fn a_wait_with_nothing_to_wait_for_is_refused() {
    let home = home_with_short_budget();
    let script = json!({ "responses": [
        call("call-1", "python", &json!({ "code": "try:\n    await jobs.wait()\nexcept RuntimeError as error:\n    print(error)" })),
        answer("Nothing ran."),
    ] });
    let (code, events, stderr) = run(home.path(), &script);
    assert_eq!(code, Some(0), "stderr: {stderr}");
    let results = texts(&events, "toolResult");
    assert_eq!(results.len(), 1, "{results:?}");
    assert!(
        results[0].contains(
            "Nothing to wait for: no job, bash() handle, subagent or message of this session is pending"
        ),
        "{results:?}"
    );
}
