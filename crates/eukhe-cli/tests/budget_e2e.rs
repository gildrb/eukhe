//! End-to-end budgets (spec/README.md B1-B9) through the real binary: an
//! isolated HOME, the scripted faux provider (`EUKHE_FAUX_SCRIPT`), the
//! `--budget-*` flags, and the ledger the run leaves (one account per
//! file, `<agent dir>/budgets/<owner session>.jsonl`, each line an
//! operation, the core's answer and the state after it).

#[path = "support/eukhe.rs"]
mod eukhe;
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::{Child, Stdio};
use std::time::{Duration, Instant};

use eukhe::eukhe_command;
use serde_json::{json, Value};

/// How long a test waits for something the run must do.
const WAIT: Duration = Duration::from_secs(60);

fn command(home: &Path, args: &[&str], script: &Value) -> std::process::Command {
    let mut command = eukhe_command();
    command
        .args(args)
        .env("HOME", home)
        .env("EUKHE_FAUX_SCRIPT", script.to_string())
        // Keep the isolated HOME authoritative.
        .env_remove("EUKHE_CODING_AGENT_DIR")
        .env_remove("EUKHE_AGENT_DIR")
        .env_remove("EUKHE_SESSION_DIR")
        .env_remove("EUKHE_CODING_AGENT_SESSION_DIR")
        .env_remove("RLM_DEPTH")
        .current_dir(home);
    command
}

fn run(home: &Path, args: &[&str], script: &Value) -> (String, String, i32) {
    output(&mut command(home, args, script))
}

fn output(command: &mut std::process::Command) -> (String, String, i32) {
    let output = command
        .stdin(Stdio::null())
        .output()
        .expect("binary present");
    (
        String::from_utf8_lossy(&output.stdout).to_string(),
        String::from_utf8_lossy(&output.stderr).to_string(),
        output.status.code().unwrap_or(-1),
    )
}

/// The default agent dir's budgets under `home`.
fn budgets(home: &Path) -> PathBuf {
    home.join(".eukhe/budgets")
}

/// The one account ledger in `dir`: its owner (the file's stem) and every
/// complete record; `None` while there is none.
fn ledger(dir: &Path) -> Option<(String, Vec<Value>)> {
    let mut files: Vec<PathBuf> = std::fs::read_dir(dir)
        .ok()?
        .flatten()
        .map(|entry| entry.path())
        .filter(|path| {
            path.extension()
                .is_some_and(|extension| extension == "jsonl")
        })
        .collect();
    assert!(files.len() <= 1, "one account, one ledger: {files:?}");
    let file = files.pop()?;
    let owner = file.file_stem()?.to_string_lossy().into_owned();
    let text = std::fs::read_to_string(&file).ok()?;
    let complete = &text[..text.rfind('\n')?];
    let records = complete
        .lines()
        .map(|line| serde_json::from_str(line).expect("a ledger line"))
        .collect();
    Some((owner, records))
}

/// The state after the last record of the one ledger in `dir`, with the
/// account's owner.
fn ledger_state(dir: &Path) -> Option<(String, Value)> {
    let (owner, records) = ledger(dir)?;
    let state = records.last()?["state"].clone();
    Some((owner, state))
}

fn amount(state: &Value, part: &str, dimension: &str) -> u64 {
    state["account"][part][dimension].as_u64().unwrap_or(0)
}

fn held(state: &Value, dimension: &str) -> u64 {
    state["account"]["holds"].as_array().map_or(0, |holds| {
        holds
            .iter()
            .map(|hold| hold["amount"][dimension].as_u64().unwrap_or(0))
            .sum()
    })
}

/// free + held + spent + lent == limit + over in `dimension`.
fn assert_balanced(state: &Value, dimension: &str) {
    let limit = state["limits"][dimension]
        .as_u64()
        .expect("a limited dimension");
    assert_eq!(
        amount(state, "free", dimension)
            + held(state, dimension)
            + amount(state, "spent", dimension)
            + amount(state, "lent", dimension),
        limit + amount(state, "over", dimension),
        "{state:#}"
    );
}

/// The phase and shortage of the agent `agent` of the account.
fn member(state: &Value, agent: &str) -> (Value, Value) {
    let member = &state["members"][agent];
    (member["phase"].clone(), member["short"].clone())
}

fn events(stdout: &str) -> Vec<Value> {
    stdout
        .lines()
        .map(|line| serde_json::from_str(line).expect("a JSON event line"))
        .collect()
}

/// What the provider billed over every assistant message the stream
/// ended: input, output, cache reads and writes.
fn billed(events: &[Value]) -> (u64, u64) {
    let answers: Vec<&Value> = events
        .iter()
        .filter(|event| event["type"] == "message_end" && event["message"]["role"] == "assistant")
        .collect();
    let tokens = answers
        .iter()
        .map(|event| {
            let usage = &event["message"]["usage"];
            ["input", "output", "cacheRead", "cacheWrite"]
                .iter()
                .map(|key| usage[*key].as_u64().unwrap_or(0))
                .sum::<u64>()
        })
        .sum();
    (tokens, answers.len() as u64)
}

fn final_answer(events: &[Value]) -> Value {
    events
        .iter()
        .rev()
        .find(|event| event["type"] == "message_end" && event["message"]["role"] == "assistant")
        .expect("a final assistant message")["message"]["content"][0]["text"]
        .clone()
}

fn read_call(path: &str) -> Value {
    json!({ "content": [{ "type": "toolCall", "name": "read", "arguments": { "i": "Reading a file", "path": path } }] })
}

/// B1, B4, B6: with one tool call left, the second call is not run, the
/// agent is told, and it still gives its final answer.
#[test]
fn a_tool_call_past_the_budget_is_not_run_and_the_agent_still_answers() {
    let home = tempfile::TempDir::new().unwrap();
    std::fs::write(home.path().join("a.txt"), "alpha\n").unwrap();
    std::fs::write(home.path().join("b.txt"), "beta\n").unwrap();
    let script =
        json!({ "responses": [read_call("a.txt"), read_call("b.txt"), "the final answer"] });
    let (stdout, stderr, code) = run(
        home.path(),
        &[
            "--budget-tool-calls",
            "1",
            "--mode",
            "json",
            "-p",
            "read both files",
        ],
        &script,
    );
    assert_eq!(code, 0, "stderr: {stderr}");
    let events = events(&stdout);
    let ends: Vec<(bool, String)> = events
        .iter()
        .filter(|event| event["type"] == "tool_execution_end")
        .map(|event| {
            let text = event["result"]["content"]
                .as_array()
                .map(|blocks| {
                    blocks
                        .iter()
                        .filter_map(|block| block["text"].as_str())
                        .collect::<String>()
                })
                .unwrap_or_default();
            (event["isError"].as_bool().unwrap_or(false), text)
        })
        .collect();
    assert_eq!(ends.len(), 2, "{ends:#?}");
    assert!(!ends[0].0 && ends[0].1.contains("alpha"), "{ends:#?}");
    assert!(
        ends[1].0 && ends[1].1.starts_with("Budget exhausted (tool calls)"),
        "{ends:#?}"
    );
    assert!(!ends[1].1.contains("beta"), "{ends:#?}");
    assert_eq!(final_answer(&events), "the final answer");
    let (owner, state) = ledger_state(&budgets(home.path())).expect("a ledger");
    assert_eq!(amount(&state, "spent", "toolCalls"), 1, "{state:#}");
    assert_eq!(
        member(&state, &owner),
        (json!("wrap_up"), json!("tool_calls")),
        "{state:#}"
    );
    assert_eq!(state["account"]["holds"], json!([]), "{state:#}");
    assert_balanced(&state, "toolCalls");
}

/// B1, B2, B6: a request whose smallest offer is past the budget is never
/// sent: no answer, exit 1, nothing spent, the agent exhausted.
#[test]
fn a_request_past_the_budget_is_never_sent() {
    let home = tempfile::TempDir::new().unwrap();
    let script = json!({ "responses": ["this must never be said"] });
    let (stdout, stderr, code) = run(
        home.path(),
        &["--budget-tokens", "50", "-p", "hello"],
        &script,
    );
    assert_eq!(code, 1, "stdout: {stdout}\nstderr: {stderr}");
    assert!(!stdout.contains("this must never be said"), "{stdout}");
    assert!(stderr.contains("Budget exhausted (tokens)"), "{stderr}");
    let (owner, state) = ledger_state(&budgets(home.path())).expect("a ledger");
    assert_eq!(amount(&state, "spent", "tokens"), 0, "{state:#}");
    assert_eq!(amount(&state, "free", "tokens"), 50, "{state:#}");
    assert_eq!(
        member(&state, &owner),
        (json!("exhausted"), json!("tokens")),
        "{state:#}"
    );
}

/// B3, B9: what the ledger reports as spent is the sum of what the
/// provider reported, one model request per answer, and the budget
/// balances.
#[test]
fn the_ledgers_total_is_the_sum_of_the_providers_usage() {
    let home = tempfile::TempDir::new().unwrap();
    let script = json!({ "responses": [read_call("a.txt"), "done"] });
    std::fs::write(home.path().join("a.txt"), "alpha\n").unwrap();
    let (stdout, stderr, code) = run(
        home.path(),
        &[
            "--budget-tokens",
            "2000000",
            "--budget-tool-calls",
            "5",
            "--budget-requests",
            "10",
            "--mode",
            "json",
            "-p",
            "read the file",
        ],
        &script,
    );
    assert_eq!(code, 0, "stderr: {stderr}");
    let (tokens, answers) = billed(&events(&stdout));
    assert!(tokens > 0, "{stdout}");
    let (owner, state) = ledger_state(&budgets(home.path())).expect("a ledger");
    assert_eq!(
        (
            amount(&state, "spent", "tokens"),
            amount(&state, "spent", "toolCalls"),
            amount(&state, "spent", "requests"),
        ),
        (tokens, 1, answers),
        "{state:#}"
    );
    assert_eq!(state["account"]["holds"], json!([]), "{state:#}");
    assert_eq!(member(&state, &owner), (json!("working"), Value::Null));
    for dimension in ["tokens", "toolCalls", "requests"] {
        assert_balanced(&state, dimension);
    }
}

/// A short `--budget-time`: a deadline closer than a work request and the
/// final answer's reserve together. The first request is refused as work
/// (time), the agent is told to wrap up, and its final answer is granted
/// and given: the run ends with that answer.
#[test]
fn a_short_deadline_wraps_the_run_up_with_its_final_answer() {
    let home = tempfile::TempDir::new().unwrap();
    let script = json!({ "responses": ["the final answer"] });
    let (stdout, stderr, code) = run(
        home.path(),
        &["--budget-time", "2m", "--mode", "json", "-p", "work on it"],
        &script,
    );
    assert_eq!(code, 0, "stdout: {stdout}\nstderr: {stderr}");
    assert_eq!(final_answer(&events(&stdout)), "the final answer");
    let (owner, records) = ledger(&budgets(home.path())).expect("a ledger");
    let state = &records.last().expect("a record")["state"];
    let open = &records[0];
    assert_eq!(
        open["op"]["deadlineMs"].as_u64(),
        open["atMs"].as_u64().map(|at| at + 120_000),
        "the deadline is 2 minutes after the budget was set: {open:#}"
    );
    let reserves: Vec<(Value, Value)> = records
        .iter()
        .filter(|record| record["op"]["kind"] == "reserve" && record["op"]["agent"] == owner)
        .map(|record| (record["op"]["use"].clone(), record["outcome"].clone()))
        .collect();
    assert!(
        reserves.iter().any(|(use_, outcome)| use_ == "work"
            && outcome
                == &json!({ "kind": "refused", "refusal": { "why": "short", "dimension": "time" } })),
        "a work request was refused for time: {reserves:#?}"
    );
    assert!(
        reserves
            .iter()
            .any(|(use_, outcome)| use_ == "final" && outcome["kind"] == "granted"),
        "the final answer was granted: {reserves:#?}"
    );
    assert_eq!(
        member(state, &owner),
        (json!("wrap_up"), json!("time")),
        "{state:#}"
    );
    assert_eq!(state["account"]["holds"], json!([]), "{state:#}");
    assert!(
        stderr.contains("wrap-up") && stderr.contains("deadline "),
        "the run's budget line names the wrap-up and the deadline: {stderr}"
    );
}

/// Stops the supervisor a headless run started on the sandbox's socket
/// when the test ends, passing or not.
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

/// The kernel cell the parent spawns its two children with: neither is
/// given a budget of its own.
const SPAWN_TWO: &str = "one = await rlm.spawn(\"lane one\", name=\"kid-one\", why=\"isolate\")\ntwo = await rlm.spawn(\"lane two\", name=\"kid-two\", why=\"isolate\")\nprint(one.rlm_child_id, two.rlm_child_id)";

/// B4: a parent that spawns two subagents without a budget of their own
/// shares its one account with them: one ledger, each child a member
/// below the parent (joined, then released when it ended, its link to the
/// parent's file gone) whose requests reserve from that account, and no
/// record of the account's life passes the root's budget.
#[test]
fn subagents_without_a_budget_draw_from_their_parents_one_account() {
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
    let script = json!({
        "responses": [
            { "content": [{ "type": "toolCall", "name": "ipython", "arguments": { "code": SPAWN_TWO } }] },
            { "text": "spawn turn done" },
            { "text": "reports seen" },
        ],
        "repeatLastResponse": true,
    });
    let agent_dir = home.path().join("agent");
    let (stdout, stderr, code) = output(
        command(
            home.path(),
            &[
                "--budget-tokens",
                "2000000",
                "--budget-requests",
                "40",
                "--mode",
                "json",
                "-p",
                "spawn the kids",
            ],
            &script,
        )
        .env("EUKHE_DAEMON_SOCKET", &socket)
        .env("EUKHE_FAUX_CHILD_SCRIPT", &child_script)
        .env("EUKHE_OFFLINE", "1")
        .env("EUKHE_CODING_AGENT_DIR", &agent_dir)
        // A supervisor the test fails to stop takes its workers down soon.
        .env(
            eukhe_daemon::worker::WORKER_SUPERVISOR_LOST_EXIT_MS_ENV,
            "15000",
        ),
    );
    assert_eq!(code, 0, "stdout: {stdout}\nstderr: {stderr}");

    let dir = agent_dir.join("budgets");
    let (owner, records) = ledger(&dir).expect("one ledger");
    let joined: BTreeSet<(String, String)> = records
        .iter()
        .filter(|record| record["op"]["kind"] == "join")
        .map(|record| {
            (
                record["op"]["agent"].as_str().unwrap().to_owned(),
                record["op"]["parent"].as_str().unwrap().to_owned(),
            )
        })
        .collect();
    let children: BTreeSet<String> = joined.iter().map(|(child, _)| child.clone()).collect();
    assert_eq!(
        (
            joined.len(),
            joined.iter().all(|(_, parent)| *parent == owner),
        ),
        (2, true),
        "two children joined below the parent: {joined:?}"
    );
    for child in &children {
        // A granted reservation, and the release when the child ended.
        let did = |kind: &str| {
            records.iter().any(|record| {
                record["op"]["kind"] == kind
                    && record["op"]["agent"] == child.as_str()
                    && (kind != "reserve" || record["outcome"]["kind"] == "granted")
            })
        };
        assert_eq!(
            (did("reserve"), did("release"), dir.join(format!("{child}.link")).exists()),
            (true, true, false),
            "the child {child} reserved from the account, was released when it ended, and links to no account"
        );
    }
    for record in &records {
        let state = &record["state"];
        for dimension in ["tokens", "requests"] {
            let limit = state["limits"][dimension].as_u64().expect("a limit");
            assert_eq!(amount(state, "over", dimension), 0, "{record:#}");
            assert!(
                amount(state, "spent", dimension) + held(state, dimension) <= limit,
                "the account passed the root's budget: {record:#}"
            );
            assert_balanced(state, dimension);
        }
    }
    let state = &records.last().expect("a record")["state"];
    assert_eq!(state["account"]["holds"], json!([]), "{state:#}");
}

struct Killed(Child);

impl Drop for Killed {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

/// B5: a run killed while its request is in flight left a reservation on
/// disk; the next run of the session charges it in full, once, and the
/// budget still balances.
#[test]
fn a_run_killed_mid_request_is_charged_its_reservation_once() {
    let home = tempfile::TempDir::new().unwrap();
    // the provider answers only after the test killed the run
    let slow = json!({ "responses": [{ "content": [{ "type": "text", "text": "too late" }], "delayMs": 600_000 }] });
    let mut child = Killed(
        command(
            home.path(),
            &["--budget-tokens", "2000000", "-p", "think for a long time"],
            &slow,
        )
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .expect("binary present"),
    );
    let dir = budgets(home.path());
    // the reservation is on disk before the request is sent
    let started = Instant::now();
    let reserved = loop {
        if let Some((_, state)) = ledger_state(&dir) {
            let reserved = held(&state, "tokens");
            if reserved > 0 {
                break reserved;
            }
        }
        assert!(
            started.elapsed() < WAIT,
            "no reservation appeared in the ledger"
        );
        assert!(
            child.0.try_wait().expect("the run's status").is_none(),
            "the run ended before it reserved"
        );
        std::thread::sleep(Duration::from_millis(20));
    };
    child.0.kill().expect("kill the run");
    child.0.wait().expect("reap the run");
    let (_, crashed) = ledger_state(&dir).expect("a ledger");
    assert_eq!(amount(&crashed, "spent", "tokens"), 0, "{crashed:#}");
    assert_eq!(held(&crashed, "tokens"), reserved, "{crashed:#}");

    // the session continues: what was in flight is charged in full
    // (the interrupted turn may be answered again before the new prompt)
    let quick = json!({ "responses": ["back"], "repeatLastResponse": true });
    let (stdout, stderr, code) = run(
        home.path(),
        &["-c", "--mode", "json", "-p", "are you there"],
        &quick,
    );
    assert_eq!(code, 0, "stderr: {stderr}");
    let (tokens, _) = billed(&events(&stdout));
    let (_, records) = ledger(&dir).expect("a ledger");
    // One recovery charged the crashed hold; any other found nothing open.
    let recoveries = records
        .windows(2)
        .filter(|pair| {
            pair[1]["op"]["kind"] == "recover"
                && amount(&pair[1]["state"], "spent", "tokens")
                    == amount(&pair[0]["state"], "spent", "tokens") + reserved
        })
        .count();
    let state = &records.last().expect("a record")["state"];
    assert_eq!(
        (amount(state, "spent", "tokens"), recoveries),
        (reserved + tokens, 1),
        "{state:#}"
    );
    assert_eq!(state["account"]["holds"], json!([]), "{state:#}");
    assert_balanced(state, "tokens");
}
