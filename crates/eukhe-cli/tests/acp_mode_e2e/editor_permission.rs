//! The editor's say on irreversible effects (spec I12): a fake editor
//! answers `session/request_permission`. An irreversible step (a `git
//! push` to a bare repository in the workspace: classed net, no network)
//! asks once and runs on allow; a rejected step and the steps after it do
//! not run and the tool result says the editor refused; a reversible step
//! asks nothing; an editor that does not serve the method is asked once,
//! never again, and the effect runs.

use super::*;

/// A daemon-attached lane whose workspace (the home, also the cwd) is a
/// git repository with one commit and a bare `remote.git` as `origin`;
/// the scripted model answers `responses` in order.
fn spawn_git_lane(responses: &[Value]) -> AcpChild {
    let home = tempfile::TempDir::new().unwrap();
    let socket = home.path().join("daemon.sock");
    let git = |args: &[&str]| {
        let status = std::process::Command::new("git")
            .args([
                "-c",
                "user.name=e2e",
                "-c",
                "user.email=e2e@example.invalid",
                "-c",
                "commit.gpgsign=false",
                "-c",
                "init.defaultBranch=main",
            ])
            .args(args)
            .current_dir(home.path())
            .env("HOME", home.path())
            .env("GIT_CONFIG_NOSYSTEM", "1")
            .status()
            .expect("git present");
        assert!(status.success(), "git {args:?}");
    };
    git(&["init", "--quiet"]);
    std::fs::write(home.path().join("README"), "e2e\n").unwrap();
    git(&["add", "README"]);
    git(&["commit", "--quiet", "-m", "first"]);
    git(&["init", "--quiet", "--bare", "remote.git"]);
    git(&["remote", "add", "origin", "./remote.git"]);
    let script = json!({ "engine": "faux", "responses": responses });
    std::fs::write(home.path().join("worker-script.json"), script.to_string()).unwrap();
    let child = daemon_attached_command(home.path(), &socket, &["--mode", "acp"])
        .spawn()
        .expect("binary present");
    AcpChild::wrap(child, Some(home), socket)
}

fn bash(script: &str) -> Value {
    json!({ "content": [
        { "type": "toolCall", "name": "bash", "arguments": { "script": script } },
    ] })
}

/// The lane's home (its socket sits there).
fn home(client: &AcpChild) -> std::path::PathBuf {
    client
        .socket
        .parent()
        .expect("the socket sits in the home")
        .to_path_buf()
}

/// Whether the bare remote has `reference`.
fn remote_has(client: &AcpChild, reference: &str) -> bool {
    std::process::Command::new("git")
        .args([
            "--git-dir",
            "remote.git",
            "rev-parse",
            "--quiet",
            "--verify",
        ])
        .arg(reference)
        .current_dir(home(client))
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .stdout(Stdio::null())
        .status()
        .expect("git present")
        .success()
}

/// One prompt turn, the client being an editor that answers each
/// `session/request_permission` with `answer(request)` (the response body:
/// a `result` or an `error`). Returns the prompt response, the permission
/// requests, and the notifications, in order.
fn prompt_as_editor(
    client: &mut AcpChild,
    session_id: &str,
    text: &str,
    mut answer: impl FnMut(&Value) -> Value,
) -> (Value, Vec<Value>, Vec<Value>) {
    let prompt = client.request(
        "session/prompt",
        &json!({ "sessionId": session_id, "prompt": [{ "type": "text", "text": text }] }),
    );
    let deadline = Instant::now() + Duration::from_mins(2);
    let mut asked = Vec::new();
    let mut notifications = Vec::new();
    loop {
        let left = deadline.saturating_duration_since(Instant::now());
        assert!(!left.is_zero(), "timed out waiting for response {prompt}");
        let line = client
            .lines
            .recv_timeout(left)
            .unwrap_or_else(|error| panic!("waiting for response {prompt}: {error}"));
        let frame: Value = serde_json::from_str(&line).expect("valid JSON line");
        if frame["method"] == "session/request_permission" {
            let mut reply = answer(&frame);
            reply["jsonrpc"] = json!("2.0");
            reply["id"] = frame["id"].clone();
            client.send(&reply);
            asked.push(frame);
            continue;
        }
        if frame.get("id").and_then(Value::as_u64) == Some(prompt)
            && (frame.get("result").is_some() || frame.get("error").is_some())
        {
            return (frame, asked, notifications);
        }
        notifications.push(frame);
    }
}

fn selected(option: &str) -> Value {
    json!({ "result": { "outcome": { "outcome": "selected", "optionId": option } } })
}

/// The text of every `tool_call_update` the turn published.
fn tool_results(notifications: &[Value]) -> String {
    notifications
        .iter()
        .filter(|frame| frame["params"]["update"]["sessionUpdate"] == "tool_call_update")
        .flat_map(|frame| {
            frame["params"]["update"]["content"]
                .as_array()
                .cloned()
                .unwrap_or_default()
        })
        .filter_map(|content| content["content"]["text"].as_str().map(str::to_string))
        .collect::<Vec<_>>()
        .join("\n")
}

#[test]
fn an_irreversible_step_asks_the_editor_once_and_runs_on_allow() {
    let mut client = spawn_git_lane(&[
        bash("git push origin HEAD:refs/heads/main"),
        json!({ "text": "pushed" }),
    ]);
    let session_id = initialize_and_new_session(&mut client);
    let (response, asked, notifications) =
        prompt_as_editor(&mut client, &session_id, "push it", |_| selected("allow"));
    assert_end_turn(&response);
    assert_eq!(asked.len(), 1, "exactly one question: {asked:?}");
    let params = &asked[0]["params"];
    assert_eq!(params["sessionId"], session_id.as_str());
    assert_eq!(
        params["toolCall"]["title"], "git push origin HEAD:refs/heads/main",
        "{params}"
    );
    assert_eq!(params["toolCall"]["status"], "pending", "{params}");
    assert_eq!(
        params["options"],
        json!([
            { "optionId": "allow", "name": "Allow", "kind": "allow_once" },
            { "optionId": "reject", "name": "Reject", "kind": "reject_once" },
        ])
    );
    // The question names the bash tool call the editor was already shown.
    let bash_call = notifications
        .iter()
        .find(|frame| frame["params"]["update"]["sessionUpdate"] == "tool_call")
        .unwrap_or_else(|| panic!("the bash tool call was published: {notifications:?}"));
    assert_eq!(
        params["toolCall"]["toolCallId"],
        bash_call["params"]["update"]["toolCallId"]
    );
    assert!(
        remote_has(&client, "refs/heads/main"),
        "the allowed push ran: {}",
        tool_results(&notifications)
    );
}

#[test]
fn a_rejected_step_and_the_steps_after_it_do_not_run() {
    let mut client = spawn_git_lane(&[
        bash("git push origin HEAD:refs/heads/main\ntouch after.txt"),
        json!({ "text": "refused" }),
    ]);
    let session_id = initialize_and_new_session(&mut client);
    let (response, asked, notifications) =
        prompt_as_editor(&mut client, &session_id, "push it", |_| selected("reject"));
    assert_end_turn(&response);
    assert_eq!(asked.len(), 1, "exactly one question: {asked:?}");
    assert!(
        !remote_has(&client, "refs/heads/main"),
        "the rejected push did not run"
    );
    assert!(
        !home(&client).join("after.txt").exists(),
        "the step after the rejected one did not run"
    );
    let results = tool_results(&notifications);
    assert!(
        results.contains("the editor refused it"),
        "the tool result says the editor refused: {results}"
    );
}

#[test]
fn a_reversible_step_asks_nothing() {
    let mut client = spawn_git_lane(&[bash("echo hi > note.txt"), json!({ "text": "written" })]);
    let session_id = initialize_and_new_session(&mut client);
    let (response, asked, _) = prompt_as_editor(&mut client, &session_id, "write a note", |_| {
        selected("reject")
    });
    assert_end_turn(&response);
    assert!(
        asked.is_empty(),
        "a workspace write asks nothing: {asked:?}"
    );
    assert_eq!(
        std::fs::read_to_string(home(&client).join("note.txt")).unwrap(),
        "hi\n"
    );
}

#[test]
fn an_editor_without_the_method_is_asked_once_and_the_effects_run() {
    let mut client = spawn_git_lane(&[
        bash("git push origin HEAD:refs/heads/first"),
        json!({ "text": "pushed first" }),
        bash("git push origin HEAD:refs/heads/second"),
        json!({ "text": "pushed second" }),
    ]);
    let session_id = initialize_and_new_session(&mut client);
    let unknown = |_: &Value| json!({ "error": { "code": -32601, "message": "Method not found" } });
    let (response, asked, _) = prompt_as_editor(&mut client, &session_id, "push first", unknown);
    assert_end_turn(&response);
    assert_eq!(asked.len(), 1, "asked once: {asked:?}");
    assert!(
        remote_has(&client, "refs/heads/first"),
        "the first push ran"
    );
    let (response, asked, _) = prompt_as_editor(&mut client, &session_id, "push second", unknown);
    assert_end_turn(&response);
    assert!(asked.is_empty(), "never asked again: {asked:?}");
    assert!(
        remote_has(&client, "refs/heads/second"),
        "the second push ran"
    );
}
