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

//! End-to-end verifier for the eval/verifiers composition over the headless
//! session: the CLI flags drive an autonomous print/json session whose
//! acceptance check is a verifier command (no eval-specific core code —
//! the composition is the `eukhe` binary itself). A fixture verifier
//! script decides completion; the checks' outcome must surface as durable
//! session rows and structured json events, and the process exit code
//! must follow the headless contract (D5, V10).

use std::path::{Path, PathBuf};

use serde_json::{json, Value};

#[path = "support/eukhe.rs"]
mod eukhe;
use eukhe::eukhe_command;

#[path = "support/durable_store.rs"]
mod durable_store;

use durable_store::{read_transcript, session_dirs, Transcript};

fn isolated_home() -> tempfile::TempDir {
    tempfile::TempDir::new().unwrap()
}

fn run(home: &Path, args: &[&str], script: &Value) -> (String, String, i32) {
    run_in(home, home, args, script)
}

/// [`run`] in the directory `home/work`: the run's workspace, which the
/// checks fingerprint, holds neither the agent dir (the session's own
/// storage) nor the fixture verifier's counter.
fn run_at_work(home: &Path, args: &[&str], script: &Value) -> (String, String, i32) {
    let work = home.join("work");
    std::fs::create_dir_all(&work).expect("work dir");
    run_in(home, &work, args, script)
}

fn run_in(home: &Path, cwd: &Path, args: &[&str], script: &Value) -> (String, String, i32) {
    let output = eukhe_command()
        .args(args)
        .env("HOME", home)
        .env("EUKHE_FAUX_SCRIPT", script.to_string())
        // Keep the isolated HOME authoritative: ambient agent/session dir
        // overrides and daemon sockets from the test environment must not
        // leak in (fresh sessions never probe the daemon; keep it that way).
        .env_remove("EUKHE_CODING_AGENT_DIR")
        .env_remove("EUKHE_SESSION_DIR")
        .env_remove("EUKHE_CODING_AGENT_SESSION_DIR")
        .env_remove("EUKHE_DAEMON_SOCKET")
        .current_dir(cwd)
        .output()
        .expect("binary present");
    (
        String::from_utf8_lossy(&output.stdout).to_string(),
        String::from_utf8_lossy(&output.stderr).to_string(),
        output.status.code().unwrap_or(-1),
    )
}

fn make_executable(path: &Path) {
    use std::os::unix::fs::PermissionsExt;
    let mut permissions = std::fs::metadata(path).unwrap().permissions();
    permissions.set_mode(0o755);
    std::fs::set_permissions(path, permissions).unwrap();
}

/// The fixture verifier that passes: the task is done. Hermetic: only the
/// fixture directory is touched.
fn passing_verifier(home: &Path) -> PathBuf {
    let script = home.join("verify.sh");
    std::fs::write(
        &script,
        "#!/usr/bin/env bash\n\
         echo \"solution verified\"\n\
         exit 0\n",
    )
    .unwrap();
    make_executable(&script);
    script
}

/// The fixture verifier that never passes: a task the scripted model cannot
/// complete.
fn always_failing_verifier(home: &Path) -> PathBuf {
    let script = home.join("verify-fail.sh");
    std::fs::write(
        &script,
        "#!/usr/bin/env bash\n\
         echo \"solution.txt missing\" >&2\n\
         exit 1\n",
    )
    .unwrap();
    make_executable(&script);
    script
}

/// The durable session storages the run left (`<sessions>/<id>/`).
fn session_files(home: &Path) -> Vec<PathBuf> {
    session_dirs(&home.join(".eukhe/sessions"))
}

/// Whether the stored session holds an `autonomous_status` row.
fn has_autonomous_status_row(transcript: &Transcript) -> bool {
    !transcript.custom_rows("autonomous_status").is_empty()
}

/// The stored user prompts' texts, in order.
fn durable_user_texts(transcript: &Transcript) -> Vec<String> {
    transcript
        .of_kind("pi.user")
        .into_iter()
        .filter_map(|entry| entry["model"].get(0).map(text_of))
        .collect()
}

/// The text of a message's content: a string or a text block list.
fn text_of(message: &Value) -> String {
    match &message["content"] {
        Value::String(text) => text.clone(),
        content => content
            .as_array()
            .and_then(|blocks| blocks.first())
            .and_then(|block| block.get("text"))
            .and_then(Value::as_str)
            .unwrap_or_default()
            .to_string(),
    }
}

fn parse_events(stdout: &str) -> Vec<Value> {
    stdout
        .lines()
        .filter(|line| !line.trim().is_empty())
        .map(|line| serde_json::from_str(line).expect("stdout line parses as json"))
        .collect()
}

/// `value` with every assistant message removed, also those nested in
/// `turn_end` and `agent_end`, and the assistant's stream (a
/// `message_update`'s `assistantMessageEvent`, whose text delta holds as much
/// of the reply as the stream coalesced): what a client shows besides the
/// model's own replies.
fn without_assistant_messages(value: &Value) -> Value {
    match value {
        Value::Array(items) => Value::Array(
            items
                .iter()
                .filter(|item| item["role"] != "assistant")
                .map(without_assistant_messages)
                .collect(),
        ),
        Value::Object(fields) => Value::Object(
            fields
                .iter()
                .filter(|(key, field)| {
                    key.as_str() != "assistantMessageEvent" && field["role"] != "assistant"
                })
                .map(|(key, field)| (key.clone(), without_assistant_messages(field)))
                .collect(),
        ),
        other => other.clone(),
    }
}

/// The acceptance returns in the stored user prompts: those that start
/// with the checks' not-verified header.
fn acceptance_returns(transcript: &Transcript) -> Vec<String> {
    durable_user_texts(transcript)
        .into_iter()
        .filter(|text| text.starts_with("[acceptance: not verified]"))
        .collect()
}

/// The verifier-driven session completing: the verifier is the run's
/// command check; the first claim passes it, and the checks' end stops the
/// run (no continuation of the run's own, which a run without checks
/// would get) without a row: the stop surfaces through the exit contract
/// only.
#[test]
fn verifier_check_pass_stops_the_run_with_structured_events_in_run() {
    let home = isolated_home();
    let verifier = passing_verifier(home.path());
    let script = json!({ "responses": ["done", "unused"] });
    let (stdout, stderr, code) = run_at_work(
        home.path(),
        &[
            "--mode",
            "json",
            "-p",
            "build the feature",
            "--auto",
            "--accept-cmd",
            verifier.to_str().unwrap(),
            "--accept-no-intent",
        ],
        &script,
    );
    assert_eq!(code, 0, "stderr: {stderr}\nstdout: {stdout}");
    let events = parse_events(&stdout);

    // Header first.
    assert_eq!(events[0]["type"], "session");
    assert_eq!(events[0]["version"], 3);

    // One answer: the claim the check confirmed.
    let assistant_texts: Vec<String> = events
        .iter()
        .filter(|event| event["type"] == "message_end" && event["message"]["role"] == "assistant")
        .map(|event| text_of(&event["message"]))
        .collect();
    assert_eq!(
        assistant_texts,
        vec!["done".to_string()],
        "events: {events:?}"
    );
    // No continuation of the run's own, no return, no autonomous_status
    // event, and the run's single `agent_end` closes it.
    assert!(
        !events.iter().any(|event| {
            event["message"]["customType"] == "autonomous_continuation"
                || event["message"]["customType"] == "director_continuation"
                || event["message"]["customType"] == "autonomous_status"
        }),
        "events: {events:?}"
    );
    let verdicts: Vec<String> = events
        .iter()
        .filter(|event| {
            event["type"] == "message_end" && event["message"]["customType"] == "eukhe.acceptance"
        })
        .map(|event| text_of(&event["message"]))
        .collect();
    assert_eq!(
        verdicts,
        vec!["Acceptance checks passed, unconfined: 1 acceptance check confirmed.".to_string()],
        "events: {events:?}"
    );
    let agent_ends = events
        .iter()
        .filter(|event| event["type"] == "agent_end")
        .count();
    assert_eq!(agent_ends, 1, "one run: {events:?}");
    assert_eq!(events.last().unwrap()["type"], "agent_end");

    // The durable session rows: the user's prompt only; the stop wrote no
    // custom entry.
    let files = session_files(home.path());
    assert_eq!(files.len(), 1, "one session storage, got {files:?}");
    let transcript = read_transcript(&files[0]);
    assert_eq!(
        durable_user_texts(&transcript),
        vec!["build the feature".to_string()]
    );
    assert!(
        !has_autonomous_status_row(&transcript),
        "entries: {:?}",
        transcript.entries
    );
}

/// A verifier that never passes, through the removed gate flags
/// (`--autonomous-gate` is `--accept-cmd`, `--autonomous-gate-retries` is
/// `--accept-returns`): the claim goes back once, then the checks end it
/// failed; the process exits one and the stop writes no row.
#[test]
fn verifier_check_failure_exhausts_returns_and_exits_one() {
    let home = isolated_home();
    let verifier = always_failing_verifier(home.path());
    let script = json!({ "responses": ["attempt one", "attempt two", "unused"] });
    let (stdout, stderr, code) = run_at_work(
        home.path(),
        &[
            "--mode",
            "json",
            "-p",
            "build the feature",
            "--autonomous",
            "--autonomous-gate",
            verifier.to_str().unwrap(),
            "--autonomous-gate-retries",
            "1",
            "--accept-no-intent",
        ],
        &script,
    );
    assert_eq!(code, 1, "stderr: {stderr}\nstdout: {stdout}");
    assert!(
        stderr.contains("--accept-cmd"),
        "the replacement named: {stderr}"
    );
    // No stdout text output in json mode: the terminal contract rides stderr.
    assert!(
        stdout
            .lines()
            .all(|line| { serde_json::from_str::<Value>(line).is_ok() }),
        "stdout is all json events: {stdout}"
    );
    let events = parse_events(&stdout);
    let assistant_texts: Vec<String> = events
        .iter()
        .filter(|event| event["type"] == "message_end" && event["message"]["role"] == "assistant")
        .map(|event| text_of(&event["message"]))
        .collect();
    assert_eq!(
        assistant_texts,
        vec!["attempt one".to_string(), "attempt two".to_string()],
        "events: {events:?}"
    );
    assert!(
        !events
            .iter()
            .any(|event| event["message"]["customType"] == "autonomous_status"),
        "events: {events:?}"
    );
    let files = session_files(home.path());
    let transcript = read_transcript(&files[0]);
    let returns = acceptance_returns(&transcript);
    assert_eq!(
        returns.len(),
        1,
        "user entries: {:?}",
        durable_user_texts(&transcript)
    );
    assert!(returns[0].contains("(return 1 of 1)"), "{}", returns[0]);
    assert!(
        !has_autonomous_status_row(&transcript),
        "entries: {:?}",
        transcript.entries
    );
}

/// Text mode prints the final answer on a passing verifier run, and stays
/// quiet about the autonomous machinery (the stop writes nothing).
#[test]
fn text_mode_verifier_pass_prints_the_final_answer() {
    let home = isolated_home();
    let verifier = passing_verifier(home.path());
    let script = json!({ "responses": ["done", "unused"] });
    let (stdout, stderr, code) = run_at_work(
        home.path(),
        &[
            "-p",
            "build the feature",
            "--auto",
            "--accept-cmd",
            verifier.to_str().unwrap(),
            "--accept-no-intent",
        ],
        &script,
    );
    assert_eq!(code, 0, "stderr: {stderr}");
    assert_eq!(stdout, "done\n");
    assert!(!stderr.contains("utonomous"), "stderr: {stderr}");

    let files = session_files(home.path());
    let transcript = read_transcript(&files[0]);
    assert!(
        !has_autonomous_status_row(&transcript),
        "entries: {:?}",
        transcript.entries
    );
    assert_eq!(
        durable_user_texts(&transcript),
        vec!["build the feature".to_string()]
    );
}

/// The removed `--autonomous-max-tokens` is a token limit of the run's
/// budget: a limit of 1 holds no first request with its final answer's
/// reserve, so the run sends nothing and exits one, naming the budget; the
/// flag's note names `--budget-tokens`; no row.
#[test]
fn autonomous_token_limit_is_the_runs_budget() {
    let home = isolated_home();
    let script = json!({ "responses": ["unused"] });
    let (stdout, stderr, code) = run(
        home.path(),
        &[
            "-p",
            "build the feature",
            "--autonomous",
            "--autonomous-max-tokens",
            "1",
        ],
        &script,
    );
    assert_eq!(code, 1, "stderr: {stderr}");
    assert_eq!(stdout, "");
    assert!(stderr.contains("--budget-tokens"), "stderr: {stderr}");
    let files = session_files(home.path());
    let transcript = read_transcript(&files[0]);
    assert!(
        !has_autonomous_status_row(&transcript),
        "entries: {:?}",
        transcript.entries
    );
}

/// Verifier observation without autonomous flags: nothing changes — the
/// plain print contract holds (the gate flags, not their absence, enable the
/// composition).
#[test]
fn plain_print_run_ignores_no_autonomous_flags() {
    let home = isolated_home();
    let script = json!({ "responses": ["single answer"] });
    let (stdout, stderr, code) = run(home.path(), &["-p", "just answer"], &script);
    assert_eq!(code, 0, "stderr: {stderr}");
    assert_eq!(stdout, "single answer\n");
    let files = session_files(home.path());
    let transcript = read_transcript(&files[0]);
    assert!(
        !has_autonomous_status_row(&transcript),
        "entries: {:?}",
        transcript.entries
    );
}

/// `/autoresearch <goal>` in json mode on a clean git checkout: the goal
/// alone is the user's message, in the event stream and in the record; the
/// mode's setup instructions reach the model in the system prompt (the
/// scripted model echoes its system prompt, at the start and again at the
/// loop's continuation), recorded once as the `autoresearch` section of a
/// `pi.system` entry, and no message a client shows carries them.
#[test]
fn autoresearch_sends_the_goal_alone_and_its_instructions_in_the_system_prompt() {
    let home = isolated_home();
    let repo = home.path();
    let git = |args: &[&str]| {
        let output = std::process::Command::new("git")
            .args([
                "-c",
                "user.name=t",
                "-c",
                "user.email=t@t",
                "-c",
                "commit.gpgsign=false",
            ])
            .args(args)
            .current_dir(repo)
            .env("HOME", repo)
            .output()
            .expect("git runs");
        assert!(output.status.success(), "git {args:?}: {output:?}");
    };
    git(&["init", "-q", "-b", "main"]);
    // The session's own files under HOME stay out of the tree.
    std::fs::write(repo.join(".gitignore"), "/.*\n").unwrap();
    std::fs::write(repo.join("fib.py"), "def fib(n):\n    return n\n").unwrap();
    git(&["add", "-A", "-f"]);
    git(&["commit", "-q", "-m", "fib"]);
    let goal = "Make fib.py faster";
    let script = json!({ "responses": [{ "systemPrompt": true }, { "systemPrompt": true }] });
    let (stdout, stderr, _code) = run(
        repo,
        &["--mode", "json", "-p", &format!("/autoresearch {goal}")],
        &script,
    );
    let events = parse_events(&stdout);
    let setup = "Autoresearch mode is on and this branch has no experiment yet.";

    // The model read the instructions in its system prompt, on the branch,
    // at the first request and at the loop's continuation.
    let echoes: Vec<String> = events
        .iter()
        .filter(|event| event["type"] == "message_end" && event["message"]["role"] == "assistant")
        .map(|event| text_of(&event["message"]))
        .filter(|text| text.contains("<autoresearch>"))
        .collect();
    assert_eq!(echoes.len(), 2, "stderr: {stderr}\nevents: {events:?}");
    for echo in &echoes {
        assert!(echo.contains(setup), "{echo}");
        assert!(echo.contains("Branch: `autoresearch/"), "{echo}");
        assert!(echo.contains("bash autoresearch.sh"), "{echo}");
    }

    // The event stream: the goal is the only user message, and nothing a
    // client shows (user rows, custom rows) carries the instructions.
    let user_texts: Vec<String> = events
        .iter()
        .filter(|event| event["type"] == "message_end" && event["message"]["role"] == "user")
        .map(|event| text_of(&event["message"]))
        .collect();
    assert_eq!(user_texts, [goal], "events: {events:?}");
    // The scripted model's echoes are assistant messages; nothing else may
    // carry the instructions.
    for event in &events {
        let shown = without_assistant_messages(event);
        assert!(
            !shown.to_string().contains(setup),
            "the instructions reached a shown event: {shown}"
        );
    }

    // The record: the person's input is the goal; the section is one
    // `pi.system` entry, the very text the model read.
    let files = session_files(repo);
    let transcript = read_transcript(&files[0]);
    let user_inputs: Vec<String> = transcript
        .of_kind("pi.user")
        .into_iter()
        .filter(|entry| entry["data"]["origin"]["kind"] != "autonomous")
        .filter_map(|entry| entry["model"].get(0).map(text_of))
        .collect();
    assert_eq!(user_inputs, [goal], "entries: {:?}", transcript.entries);
    let sections: Vec<&str> = transcript
        .of_kind("pi.system")
        .into_iter()
        .filter_map(|entry| entry["model"][0]["sections"]["autoresearch"].as_str())
        .collect();
    assert_eq!(sections.len(), 1, "entries: {:?}", transcript.entries);
    assert!(
        sections[0].starts_with("<autoresearch>\n"),
        "{}",
        sections[0]
    );
    for echo in &echoes {
        assert!(echo.contains(sections[0]), "{echo}");
    }
}
