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

/// free + held + (spent − mark) + lent == limit + over in `dimension`:
/// the run's limit holds what it spent since it started (`mark`, the
/// account's spend at its start, B19).
fn assert_balanced(state: &Value, dimension: &str) {
    let limit = state["limits"][dimension]
        .as_u64()
        .expect("a limited dimension");
    let mark = state["mark"][dimension].as_u64().unwrap_or(0);
    assert_eq!(
        amount(state, "free", dimension)
            + held(state, dimension)
            + (amount(state, "spent", dimension) - mark)
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

/// B6, B8, B15: with limits on, the run's first request carries the
/// notice of its limits (written before the request reads its context, so
/// before the answer); with limits off it carries none. The faux model
/// answers with the request's user text; `-p` prints that answer (text
/// mode: on stdout; JSON mode: the last assistant message) and exits 0.
#[test]
fn the_first_request_carries_the_limits_notice_only_with_limits_on() {
    const NOTICE: &str = "[budget] This task has a budget: ";
    for limits in ["on", "off"] {
        for mode in ["text", "json"] {
            let home = tempfile::TempDir::new().unwrap();
            std::fs::create_dir_all(home.path().join(".eukhe")).unwrap();
            std::fs::write(
                home.path().join(".eukhe/settings.json"),
                json!({ "budget": { "limits": limits } }).to_string(),
            )
            .unwrap();
            let script = json!({ "responses": [{ "userText": true }] });
            let (stdout, stderr, code) =
                run(home.path(), &["--mode", mode, "-p", "answer me"], &script);
            assert_eq!(
                code, 0,
                "{limits} {mode}: stdout: {stdout}\nstderr: {stderr}"
            );
            assert_eq!(
                stderr.contains("(limits on)"),
                limits == "on",
                "{limits} {mode}: {stderr}"
            );
            let answer = if mode == "text" {
                stdout.clone()
            } else {
                final_answer(&events(&stdout))
                    .as_str()
                    .expect("a text answer")
                    .to_owned()
            };
            assert!(answer.contains("answer me"), "{limits} {mode}: {stdout}");
            assert_eq!(
                answer.contains(NOTICE),
                limits == "on",
                "{limits} {mode}: the first request's user text: {answer}"
            );
        }
    }
}

/// B17, B1: limits that cannot hold the run's first request beside its
/// final answer's reserve send nothing: no answer, exit 1, nothing spent
/// or held, and the error names the short dimension and its limit.
#[test]
fn a_first_request_past_the_budget_is_never_sent() {
    let home = tempfile::TempDir::new().unwrap();
    let script = json!({ "responses": ["this must never be said"] });
    let (stdout, stderr, code) = run(
        home.path(),
        &["--budget-tokens", "50", "-p", "hello"],
        &script,
    );
    assert_eq!(code, 1, "stdout: {stdout}\nstderr: {stderr}");
    assert!(!stdout.contains("this must never be said"), "{stdout}");
    assert!(
        stderr.contains("Budget too small for the run's first request: tokens limit 50;")
            && stderr.contains("Nothing was sent."),
        "{stderr}"
    );
    let (_, state) = ledger_state(&budgets(home.path())).expect("a ledger");
    assert_eq!(amount(&state, "spent", "tokens"), 0, "{state:#}");
    assert_eq!(amount(&state, "free", "tokens"), 50, "{state:#}");
    assert_eq!(state["account"]["holds"], json!([]), "{state:#}");
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

/// B17, B14: a `--budget-time` (40 s) shorter than the first request's
/// floor (30 s) and the final answer's reserve (20 s) together sends
/// nothing: no answer, exit 1, nothing reserved, the deadline 40 s after
/// the run started, and the error names time, its limit and the reserve.
#[test]
fn a_deadline_below_the_first_request_and_its_reserve_sends_nothing() {
    let home = tempfile::TempDir::new().unwrap();
    let script = json!({ "responses": ["this must never be said"] });
    let (stdout, stderr, code) = run(
        home.path(),
        &["--budget-time", "40s", "--mode", "json", "-p", "work on it"],
        &script,
    );
    assert_eq!(code, 1, "stdout: {stdout}\nstderr: {stderr}");
    assert!(!stdout.contains("this must never be said"), "{stdout}");
    assert!(
        stderr.contains("Budget too small for the run's first request: time limit 40s;")
            && stderr.contains("the final answer keeps 20s. Nothing was sent."),
        "{stderr}"
    );
    let (_, records) = ledger(&budgets(home.path())).expect("a ledger");
    let open = &records[0];
    assert_eq!(
        open["op"]["deadlineMs"].as_u64(),
        open["atMs"].as_u64().map(|at| at + 40_000),
        "the deadline is 40 seconds after the budget was set: {open:#}"
    );
    assert!(
        records
            .iter()
            .all(|record| record["op"]["kind"] != "reserve"),
        "nothing was reserved: {records:#?}"
    );
    let state = &records.last().expect("a record")["state"];
    assert_eq!(state["account"]["holds"], json!([]), "{state:#}");
    assert!(
        stderr.contains("deadline "),
        "the run's budget line names the deadline: {stderr}"
    );
}

/// B14, B1: a `--budget-time` (60 s) that holds the first request (its
/// 30 s floor and the final answer's 20 s reserve) but whose deadline comes
/// within them mid-run: the first request answers after 12 s with a tool
/// call, which runs; the next work request is refused for time, the agent
/// is told to wrap up, and its final answer is granted and given: the run
/// ends with that answer before its deadline.
#[test]
fn a_deadline_reached_mid_run_wraps_it_up_with_its_final_answer() {
    let home = tempfile::TempDir::new().unwrap();
    std::fs::write(home.path().join("a.txt"), "alpha\n").unwrap();
    let mut slow_call = read_call("a.txt");
    slow_call["delayMs"] = json!(12_000);
    let script = json!({ "responses": [slow_call, "the final answer"] });
    let started = Instant::now();
    let (stdout, stderr, code) = run(
        home.path(),
        &["--budget-time", "60s", "--mode", "json", "-p", "work on it"],
        &script,
    );
    assert_eq!(code, 0, "stdout: {stdout}\nstderr: {stderr}");
    assert!(
        started.elapsed() < Duration::from_secs(60),
        "the run ended before its deadline"
    );
    let events = events(&stdout);
    assert_eq!(final_answer(&events), "the final answer");
    assert!(
        events
            .iter()
            .any(|event| event["type"] == "tool_execution_end"
                && event["isError"] == json!(false)
                && event["result"].to_string().contains("alpha")),
        "the first request's tool call ran: {stdout}"
    );
    let (owner, records) = ledger(&budgets(home.path())).expect("a ledger");
    let reserves: Vec<(Value, Value)> = records
        .iter()
        .filter(|record| record["op"]["kind"] == "reserve" && record["op"]["agent"] == owner)
        .map(|record| (record["op"]["use"].clone(), record["outcome"].clone()))
        .collect();
    assert!(
        reserves
            .first()
            .is_some_and(|(use_, outcome)| use_ == "work" && outcome["kind"] == "granted"),
        "the first work request was granted: {reserves:#?}"
    );
    assert!(
        reserves.iter().any(|(use_, outcome)| use_ == "work"
            && outcome
                == &json!({ "kind": "refused", "refusal": { "why": "short", "dimension": "time" } })),
        "a later work request was refused for time: {reserves:#?}"
    );
    assert!(
        reserves
            .last()
            .is_some_and(|(use_, outcome)| use_ == "final" && outcome["kind"] == "granted"),
        "the final answer was granted last: {reserves:#?}"
    );
    let state = &records.last().expect("a record")["state"];
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
        let Ok(mut stream) = eukhe_types::platform::transport::connect_blocking(
            &self.socket,
            eukhe_bend::rules::server_peer::PEER_RULES,
        ) else {
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

/// The kernel cell the parent spawns its two children with: neither names
/// a budget of its own.
const SPAWN_TWO: &str = "one = await rlm.spawn(\"lane one\", name=\"kid-one\")\ntwo = await rlm.spawn(\"lane two\", name=\"kid-two\")\nprint(one.rlm_child_id, two.rlm_child_id)";

/// Every account ledger in `dir`: its owner (the file's stem) and every
/// complete record.
fn ledgers(dir: &Path) -> Vec<(String, Vec<Value>)> {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return Vec::new();
    };
    entries
        .flatten()
        .map(|entry| entry.path())
        .filter(|path| {
            path.extension()
                .is_some_and(|extension| extension == "jsonl")
        })
        .filter_map(|file| {
            let owner = file.file_stem()?.to_string_lossy().into_owned();
            let text = std::fs::read_to_string(&file).ok()?;
            let complete = &text[..text.rfind('\n')?];
            let records = complete
                .lines()
                .map(|line| serde_json::from_str(line).expect("a ledger line"))
                .collect();
            Some((owner, records))
        })
        .collect()
}

/// B4 under the agent tree (T14): a parent with a budget that asks two
/// read-only helpers gives each its own budget, carved from its one
/// account (the tree gives every child a limit under a limited parent):
/// the parent's ledger records a carve for each child and its reclaim
/// when the child ended, each child's account is its own ledger, and no
/// record of the parent's account passes the root's budget.
#[test]
fn a_parents_helpers_are_carved_from_its_one_account() {
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
            { "content": [{ "type": "toolCall", "name": "python", "arguments": { "code": SPAWN_TWO } }] },
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

    let all = ledgers(&agent_dir.join("budgets"));
    let ops = |records: &[Value], kind: &str| -> BTreeSet<String> {
        records
            .iter()
            .filter(|record| record["op"]["kind"] == kind)
            .filter_map(|record| record["op"]["child"].as_str().map(str::to_owned))
            .collect()
    };
    let parents: Vec<&(String, Vec<Value>)> = all
        .iter()
        .filter(|(_, records)| !ops(records, "carve").is_empty())
        .collect();
    assert_eq!(parents.len(), 1, "one account carves: {all:#?}");
    let (owner, records) = parents[0];
    let carved = ops(records, "carve");
    let owners: BTreeSet<String> = all.iter().map(|(owner, _)| owner.clone()).collect();
    assert_eq!(
        (
            carved.len(),
            ops(records, "reclaim") == carved,
            carved.iter().all(|child| owners.contains(child)),
            all.len(),
        ),
        (2, true, true, 3),
        "the parent {owner} carved two children, each with its own ledger, and reclaimed both"
    );
    for record in records {
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
