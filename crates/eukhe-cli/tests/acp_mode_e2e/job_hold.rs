//! The ACP settle holds for running jobs: a turn that ends while a `bash`
//! script it started still runs (the script outlived the blocking budget
//! and became a job) is not quiescent. The completion names the job, the
//! job's end wakes the session inside the hold, and only then does the
//! terminal frame (naming no work) and the `end_turn` answer come.

use super::*;

/// The lane's blocking budget: the script outlives it and detaches.
const BUDGET_MS: u64 = 300;

/// A daemon-attached child whose turn starts a script that detaches, ends
/// with a status reply, and whose wake turn (the script's settle notice)
/// answers `woken`.
fn spawn_job_lane() -> AcpChild {
    let home = tempfile::TempDir::new().unwrap();
    let socket = home.path().join("daemon.sock");
    let script = json!({
        "engine": "faux",
        "responses": [
            { "content": [
                { "type": "toolCall", "name": "bash", "arguments": { "script": "sleep 3; echo built" } },
            ] },
            { "text": "the build runs in the background" },
            { "text": "woken: the build finished" },
        ],
    });
    std::fs::write(home.path().join("worker-script.json"), script.to_string()).unwrap();
    // The cwd is the home, so its `.eukhe` is both the agent dir and the
    // project config dir: the short budget and the script's auto `exec`
    // apply either way.
    let config_dir = home.path().join(".eukhe");
    std::fs::create_dir_all(&config_dir).unwrap();
    std::fs::write(
        config_dir.join("settings.json"),
        json!({
            "toolBlockingBudgetMs": BUDGET_MS,
            "shell": { "autoEffects": ["read", "exec"] },
        })
        .to_string(),
    )
    .unwrap();
    let child = daemon_attached_command(home.path(), &socket, &["--mode", "acp"])
        .spawn()
        .expect("binary present");
    AcpChild::wrap(child, Some(home), socket)
}

/// Regression (the drill's "`end_turn` at 31 s while a 45 s job ran"): the
/// completion reports the running job, the job's wake turn drains inside
/// the hold, and the terminal frame and `end_turn` come after it.
#[test]
fn acp_prompt_holds_until_a_running_job_wakes_the_session() {
    let mut client = spawn_job_lane();
    let session_id = initialize_and_new_session(&mut client);
    let prompt = client.request(
        "session/prompt",
        &json!({ "sessionId": session_id, "prompt": [{ "type": "text", "text": "run the build" }] }),
    );
    // Readiness is the completion update itself: the turn ended, the
    // detached script still runs.
    let completion = client.wait_frame(TIMEOUT, |frame| {
        let meta = update_meta(frame);
        meta["phase"] == "event" && !meta["quiescence"].is_null()
    });
    let waiting = &update_meta(&completion)["quiescence"]["waitingOn"];
    let jobs = waiting["jobs"]
        .as_array()
        .unwrap_or_else(|| panic!("the completion names the running job: {completion}"));
    assert_eq!(
        (jobs.len(), waiting["subagents"].as_u64()),
        (1, Some(0)),
        "one running job, no subagent: {completion}"
    );
    // The job's wake turn drains inside the hold: its answer lands between
    // the completion and the terminal.
    let mut woken = false;
    let terminal = client.wait_frame(TIMEOUT, |frame| {
        if update_meta(frame)["phase"] != "terminalQuiescence" {
            woken |= frame["params"]["update"]["content"]["text"]
                .as_str()
                .is_some_and(|text| text.contains("woken"));
            return false;
        }
        true
    });
    assert!(
        woken,
        "the job's wake turn ran before the terminal frame: {terminal}"
    );
    assert_eq!(
        update_meta(&terminal)["quiescence"],
        json!({ "outstandingSubagents": 0, "remainingAutonomousContinuations": 0 }),
        "the terminal names no running work: {terminal}"
    );
    let (prompt_response, updates) = client.wait_response(prompt, TIMEOUT);
    assert!(
        updates.is_empty(),
        "the terminal frame is the last notification before the response: {updates:?}"
    );
    assert_end_turn(&prompt_response);
}
