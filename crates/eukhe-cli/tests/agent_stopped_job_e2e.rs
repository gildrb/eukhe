//! A job the agent itself stopped never wakes the session: the real binary
//! in print mode, an isolated HOME, the scripted faux provider
//! (`EUKHE_FAUX_SCRIPT`), a real kernel and a 500 ms blocking budget.
//!
//! Before, the agent's own `handle.kill()` on a background `bash()` dev
//! server settled as `[bash-done ... stopped-by:agent]` with "Resume your
//! work using the result below.", which woke the session after its final
//! answer into a turn that repeated the report; and a `jobs.cancel` that
//! saw its job settle still delivered a `[job-settled ...]` notice.

use std::path::Path;

use serde_json::{json, Value};

#[path = "support/eukhe.rs"]
mod eukhe;
use eukhe::eukhe_command;

// The drill's first final answer, which the stop walk let stand.
const ANSWER: &str = "The change is in my local copy and the checks pass. I stopped the dev server.\n\nNext: look at it on the local dev server, then tell me whether to commit and deploy.";
// The drill's woken turn, which repeated the report.
const WOKEN: &str = "The dev server stopped because I shut it down. Nothing else changed.";

/// An isolated home whose agent dir runs calls on a 500 ms blocking budget.
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

/// Run `script` in print mode (json stream): the exit code and the events.
fn run(home: &Path, script: &Value) -> (Option<i32>, Vec<Value>, String) {
    let output = eukhe_command()
        .args([
            "--mode",
            "json",
            "-p",
            "Add the hairline, check it, report.",
        ])
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

fn call(id: &str, code: &str) -> Value {
    json!({ "content": [{ "type": "toolCall", "name": "python", "id": id, "arguments": { "code": code } }],
            "stopReason": "toolUse" })
}

fn answer(text: &str) -> Value {
    json!({ "content": [{ "type": "text", "text": text }], "stopReason": "stop" })
}

/// The finished messages of `role` that carry text, as their first text
/// (an assistant message of only a tool call has none).
fn texts(events: &[Value], role: &str) -> Vec<String> {
    events
        .iter()
        .filter(|event| event["type"] == "message_end" && event["message"]["role"] == role)
        .filter_map(|event| {
            let content = &event["message"]["content"];
            content
                .as_array()
                .and_then(|blocks| blocks.iter().find_map(|block| block["text"].as_str()))
                .or_else(|| content.as_str())
                .map(str::to_owned)
        })
        .collect()
}

/// Every finished message text that tells the model to resume its work.
fn resume_prompts(events: &[Value]) -> Vec<String> {
    events
        .iter()
        .filter(|event| event["type"] == "message_end")
        .map(|event| event["message"].to_string())
        .filter(|message| message.contains("Resume your work"))
        .collect()
}

/// The session's drill: a dev server started with `bash()` in one cell,
/// stopped with `.kill()` in the next, then the final answer. The server
/// takes a second to exit after its SIGTERM, so it settles after the
/// answer, as the drill's did. Only the answer is printed: no woken turn
/// repeats it.
#[test]
fn a_bash_command_the_agent_killed_does_not_wake_the_session() {
    let home = home_with_short_budget();
    let script = json!({ "responses": [
        call("call-1", "srv = bash(\"trap 'sleep 1; exit 143' TERM; sleep 30 & wait\")\nprint(srv.running)"),
        call("call-2", "srv.kill()"),
        answer(ANSWER),
        answer(WOKEN),
    ] });
    let (code, events, stderr) = run(home.path(), &script);
    assert_eq!(code, Some(0), "stderr: {stderr}");
    assert_eq!(texts(&events, "assistant"), vec![ANSWER.to_owned()]);
    assert_eq!(resume_prompts(&events), Vec::<String>::new());
}

/// A detached `bash` tool script the agent stops with `jobs.cancel`: the
/// cancel's reply carries how it ended; no `[job-settled ...]` notice
/// follows.
#[test]
fn a_job_the_agent_cancelled_sends_no_notice() {
    let home = home_with_short_budget();
    let script = json!({ "responses": [
        json!({ "content": [{ "type": "toolCall", "name": "bash", "id": "call-1",
            "arguments": { "script": "sleep 30" } }], "stopReason": "toolUse" }),
        call("call-2", "job = (await jobs.list())[0]\nprint((await jobs.cancel(job)).state)"),
        answer("Cancelled the stuck script."),
        answer(WOKEN),
    ] });
    let (code, events, stderr) = run(home.path(), &script);
    assert_eq!(code, Some(0), "stderr: {stderr}");
    let results = texts(&events, "toolResult");
    assert_eq!(results.len(), 2, "{results:?}");
    assert_eq!(results[1], "killed\n", "{results:?}");
    assert_eq!(
        texts(&events, "assistant"),
        vec!["Cancelled the stuck script.".to_owned()]
    );
    assert_eq!(resume_prompts(&events), Vec::<String>::new());
}
