//! CLI session options, threshold and overflow compaction, RLM subagent
//! settle, heartbeats, and user bash.

use super::*;

#[test]
fn acp_daemon_attached_forwards_cli_session_options() {
    // --append-system-prompt and --skill land in the daemon worker's system
    // prompt, and --autonomous-max-turns 1 stops the run.
    // Outside the agent dir: only --skill loads it.
    let skill_home = tempfile::TempDir::new().unwrap();
    let skill_dir = skill_home.path().join("argv-skill");
    std::fs::create_dir_all(&skill_dir).unwrap();
    std::fs::write(
        skill_dir.join("SKILL.md"),
        "---\nname: acp-argv-probe\ndescription: probe\n---",
    )
    .unwrap();
    let skill = skill_dir.to_str().unwrap().to_string();
    let mut client = AcpChild::spawn(
        &[
            "--mode",
            "acp",
            "--no-session",
            "--append-system-prompt",
            "ACP_ARGV_MARKER",
            "--skill",
            &skill,
            "--autonomous",
            "--autonomous-max-turns",
            "1",
        ],
        &json!({ "engine": "faux", "responses": ["one turn, then the limit stops"] }),
    );
    let socket = client.socket.clone();
    let init = client.request("initialize", &initialize_params());
    let _ = client.wait_response(init, TIMEOUT);
    let new = client.request("session/new", &json!({ "mcpServers": [] }));
    let (new_response, _) = client.wait_response(new, TIMEOUT);
    let list = daemon_request(&socket, "argv-list", &json!({ "type": "list" }));
    let active_session_id = &list["data"]["sessions"][0]["activeSessionId"];
    let get_prompt = json!({ "type": "get_system_prompt", "activeSessionId": active_session_id });
    let reply = daemon_request(&socket, "argv-prompt", &get_prompt);
    let system_prompt = reply["data"]["systemPrompt"].as_str().unwrap_or_else(|| {
        panic!("the worker's system prompt: {reply} (list: {list}, new: {new_response})")
    });
    assert!(
        system_prompt.contains("ACP_ARGV_MARKER"),
        "--append-system-prompt reaches the worker"
    );
    assert!(
        system_prompt.contains("<name>acp-argv-probe</name>"),
        "--skill reaches the worker"
    );
    let turn = client.request(
        "session/prompt",
        &json!({ "sessionId": new_response["result"]["sessionId"], "prompt": [{ "type": "text", "text": "say something" }] }),
    );
    let (turn_response, _) = client.wait_response(turn, Duration::from_mins(2));
    assert_eq!(
        turn_response["result"],
        json!({ "stopReason": "max_turn_requests" })
    );
    drop(client);
}

/// Spawn with compaction settings written into the worker's agent dir
/// (`<home>/.eukhe`: the worker inherits the child's HOME).
fn spawn_with_compaction_settings(
    args: &[&str],
    script: &serde_json::Value,
    reserve_tokens: u64,
    keep_recent_tokens: u64,
) -> AcpChild {
    let home = tempfile::TempDir::new().unwrap();
    std::fs::create_dir_all(home.path().join(".eukhe")).expect("agent dir");
    std::fs::write(
        home.path().join(".eukhe/settings.json"),
        json!({
            "compaction": {
                "enabled": true,
                "reserveTokens": reserve_tokens,
                "keepRecentTokens": keep_recent_tokens,
            }
        })
        .to_string(),
    )
    .expect("write settings.json");
    let socket = home.path().join("daemon.sock");
    std::fs::write(home.path().join("worker-script.json"), script.to_string()).unwrap();
    let child = daemon_attached_command(home.path(), &socket, args)
        .spawn()
        .expect("binary present");
    AcpChild::wrap(child, Some(home), socket)
}

/// The compaction metas among a turn's updates (the ACP `compaction_end`
/// mapping; a ran compaction carries `tokensBefore`/`summary`, every
/// skipped, failed, or cancelled run the empty payload).
fn compaction_metas(updates: &[Value]) -> Vec<Value> {
    updates
        .iter()
        .filter_map(|update| {
            let meta = &update["params"]["update"]["_meta"]["com.eukhe"];
            Some(meta["compaction"].clone()).filter(|value| !value.is_null())
        })
        .collect()
}

/// The threshold arm on the ACP turn path (pi-durable's pre-request
/// check): a prompt whose context crosses the reserve headroom compacts
/// before its request and publishes the `compaction` meta with the
/// summarizer's text.
///
/// Two turns over a 500-token combined ceiling (the f14 battery shape:
/// the window minus the faux harness model's `4_096` per-request output
/// budget and the reserve). Turn one crosses it with only its own prompt
/// in context: pi-durable finds nothing before the prompt to summarize and
/// runs no compaction (no meta; the old engine's post-turn arm published a
/// skip). Turn two's request crosses it again: the compaction summarizes
/// turn one before turn two's answer, so the summary is the second
/// scripted response.
#[test]
fn acp_threshold_auto_compaction_publishes_the_compaction_meta() {
    let script = json!({
        "engine": "faux",
        "contextWindow": 128_000,
        "maxTokens": 4_096,
        "responses": [
            { "text": "turn one reply" },
            { "text": "the auto summary" },
            { "text": "turn two reply" },
        ]
    });
    let mut client = spawn_with_compaction_settings(
        &["--mode", "acp", "--no-session"],
        &script,
        128_000 - 4_096 - 500,
        10,
    );
    let init = client.request("initialize", &initialize_params());
    let _ = client.wait_response(init, TIMEOUT);
    let new = client.request("session/new", &json!({ "mcpServers": [] }));
    let (new_response, _) = client.wait_response(new, TIMEOUT);
    let session_id = new_response["result"]["sessionId"]
        .as_str()
        .unwrap()
        .to_string();

    // Turn one crosses the headroom with nothing before it to summarize:
    // no compaction runs, and the turn answers.
    let prompt = client.request(
        "session/prompt",
        &json!({
            "sessionId": session_id,
            "prompt": [{ "type": "text", "text": format!("turn one {}", "x".repeat(8_000)) }],
        }),
    );
    let (prompt_response, updates) = client.wait_response(prompt, TIMEOUT);
    assert_end_turn(&prompt_response);
    let metas = compaction_metas(&updates);
    assert!(metas.is_empty(), "nothing to compact yet: {metas:?}");
    let answer: String = updates
        .iter()
        .filter(|update| update["params"]["update"]["sessionUpdate"] == "agent_message_chunk")
        .filter_map(|update| update["params"]["update"]["content"]["text"].as_str())
        .collect();
    assert_eq!(answer, "turn one reply");

    // Turn two's boundary: the compaction summarizes turn one and
    // publishes its result.
    let prompt = client.request(
        "session/prompt",
        &json!({
            "sessionId": session_id,
            "prompt": [{ "type": "text", "text": "turn two" }],
        }),
    );
    let (prompt_response, updates) = client.wait_response(prompt, TIMEOUT);
    assert_end_turn(&prompt_response);
    let metas = compaction_metas(&updates);
    let ran = metas
        .iter()
        .find(|meta| {
            meta["summary"]
                .as_str()
                .is_some_and(|summary| summary.contains("the auto summary"))
        })
        .unwrap_or_else(|| panic!("the compaction ran and published: {metas:?}"));
    assert!(ran["tokensBefore"].as_u64().unwrap() > 0);
}

/// A settled turn's response implies the next prompt is admissible: the
/// turn releases the session's single-prompt slot before its reply
/// leaves, so a client that prompts again the instant it reads the
/// response is admitted. Twenty back-to-back prompts keep every
/// settle-to-next-admission window covered.
#[test]
fn acp_settled_prompt_immediately_admits_the_next_prompt() {
    let script = json!({
        "engine": "faux",
        "contextWindow": 128_000,
        "responses": (0..30)
            .map(|index| json!({ "text": format!("settled turn reply {index}") }))
            .collect::<Vec<_>>(),
    });
    let mut client = AcpChild::spawn(&["--mode", "acp", "--no-session"], &script);
    let init = client.request("initialize", &initialize_params());
    let _ = client.wait_response(init, TIMEOUT);
    let new = client.request("session/new", &json!({ "mcpServers": [] }));
    let (new_response, _) = client.wait_response(new, TIMEOUT);
    let session_id = new_response["result"]["sessionId"]
        .as_str()
        .unwrap()
        .to_string();
    for turn in 0..20 {
        let prompt = client.request(
            "session/prompt",
            &json!({
                "sessionId": session_id,
                "prompt": [{ "type": "text", "text": format!("settled turn {turn}") }],
            }),
        );
        let (prompt_response, _) = client.wait_response(prompt, TIMEOUT);
        assert_eq!(
            prompt_response["result"]["stopReason"], "end_turn",
            "turn {turn}: the settled turn raced the next prompt's admission: {prompt_response}"
        );
    }
}

/// The overflow arm on the ACP turn path: a provider context-overflow
/// error runs one compact-and-retry at the boundary and the retried turn
/// settles the prompt with `end_turn` instead of the error (TS
/// `_checkCompaction` Case 1, binary level).
#[test]
fn acp_overflow_recovery_compacts_and_retries_the_turn() {
    let script = json!({
        "engine": "faux",
        "contextWindow": 128_000,
        "responses": [
            { "text": "seed reply" },
            {
                "text": "",
                "stopReason": "error",
                "errorMessage": "prompt is too long: 213462 tokens > 200000 maximum",
            },
            { "text": "the summary" },
            { "text": "recovered reply" },
        ]
    });
    let mut client =
        spawn_with_compaction_settings(&["--mode", "acp", "--no-session"], &script, 1, 10);
    let init = client.request("initialize", &initialize_params());
    let _ = client.wait_response(init, TIMEOUT);
    let new = client.request("session/new", &json!({ "mcpServers": [] }));
    let (new_response, _) = client.wait_response(new, TIMEOUT);
    let session_id = new_response["result"]["sessionId"]
        .as_str()
        .unwrap()
        .to_string();

    // The seed turn: nothing fires (context far below the headroom).
    let prompt = client.request(
        "session/prompt",
        &json!({
            "sessionId": session_id,
            "prompt": [{ "type": "text", "text": format!("seed turn {}", "x".repeat(48_000)) }],
        }),
    );
    let (prompt_response, updates) = client.wait_response(prompt, TIMEOUT);
    assert_eq!(prompt_response["result"]["stopReason"], "end_turn");
    assert!(
        compaction_metas(&updates).is_empty(),
        "nothing fires below the headroom"
    );

    // The overflow probe: the arm compacts once (the summarizer consumed
    // the third scripted response) and the retried turn recovers. The
    // daemon path releases the prompt slot before it answers the seed
    // turn, so the probe cannot bounce off the running-turn guard.
    let prompt = client.request(
        "session/prompt",
        &json!({
            "sessionId": session_id,
            "prompt": [{ "type": "text", "text": format!("overflow probe {}", "x".repeat(2_000)) }],
        }),
    );
    let (prompt_response, updates) = client.wait_response(prompt, TIMEOUT);
    assert_eq!(
        prompt_response["result"],
        json!({ "stopReason": "end_turn" }),
        "the retry recovered the turn: {prompt_response}"
    );
    let metas = compaction_metas(&updates);
    assert_eq!(metas.len(), 1, "one compaction meta: {metas:?}");
    assert_eq!(metas[0]["summary"], "the summary");
    assert!(metas[0]["tokensBefore"].as_u64().unwrap() > 0);
}

/// The namespaced eukhe payload of one session/update frame.
fn update_meta(frame: &Value) -> &Value {
    &frame["params"]["update"]["_meta"]["com.eukhe"]
}

/// The kernel cell of the spawn turn (the worker's
/// `rlm_quiescence_barrier_e2e` lane): spawn one RLM child through the
/// product `rlm.spawn` surface and record its child id.
fn spawn_cell() -> &'static str {
    "handle = await rlm.spawn(\"run the lane task\", name=\"kid\")\nprint(handle.rlm_child_id)"
}

/// The parent faux script whose turns run the spawn cell; the third
/// response answers the settled child's terminal-notice turn (the no-reply
/// notice the watcher queues on the parent).
fn spawn_parent_script(spawn_cell: &str) -> Value {
    json!({
        "engine": "faux",
        "responses": [
            { "content": [
                { "type": "toolCall", "name": "ipython", "arguments": { "code": spawn_cell } },
            ] },
            { "text": "spawn turn done" },
            { "text": "notice seen" },
        ],
    })
}

/// One scripted-children lane: a daemon-attached resident session whose
/// parent turns spawn a held scripted child (resident because the RLM spawn
/// ledger needs the parent's session file — a `--no-session` parent cannot
/// spawn children). The parent's active session id is read at setup, before
/// the spawn: once a child runs, `live_sessions` lists both workers.
fn spawn_lane(
    args: &[&str],
    child_hold_ms: u64,
    kernel_python: &std::path::Path,
) -> (AcpChild, String, String) {
    let parent = spawn_parent_script(spawn_cell());
    let child_script = json!({ "responses": [ { "text": "kid done", "delayMs": child_hold_ms } ] });
    let mut client = AcpChild::spawn_with_child_script(args, &parent, &child_script, kernel_python);
    let init = client.request("initialize", &initialize_params());
    let _ = client.wait_response(init, TIMEOUT);
    let session_id = new_session(&mut client);
    let socket = client.socket.clone();
    let active_session_id = live_sessions(&socket).remove(0)["activeSessionId"]
        .as_str()
        .expect("the parent session id")
        .to_string();
    (client, session_id, active_session_id)
}

/// The ACP settle waits for RLM quiescence (TS #1612): the completion
/// update reports the live outstanding-subagent count, the terminal update
/// reports zero, and the settled child's terminal-notice turn ("notice
/// seen") drains inside the barrier, between the two.
#[test]
fn acp_prompt_settles_after_rlm_quiescence() {
    let Some(kernel_python) = kernel_python() else {
        return;
    };
    let (mut client, session_id, _) = spawn_lane(&["--mode", "acp"], 5_000, &kernel_python);
    let prompt = client.request(
        "session/prompt",
        &json!({ "sessionId": session_id, "prompt": [{ "type": "text", "text": "spawn the kid" }] }),
    );
    // Readiness is the completion update itself: the parent turn settled,
    // the held child turn is still in flight.
    let completion = client.wait_frame(TIMEOUT, |frame| {
        let meta = update_meta(frame);
        meta["phase"] == "event" && !meta["quiescence"].is_null()
    });
    assert_eq!(
        update_meta(&completion)["quiescence"]["outstandingSubagents"],
        1,
        "the completion reports the live child: {completion}"
    );
    // The settled child's terminal-notice turn drains inside the barrier:
    // its streamed answer lands between the completion and the terminal.
    let mut notice_seen = false;
    let terminal = client.wait_frame(TIMEOUT, |frame| {
        let meta = update_meta(frame);
        if meta["phase"] != "terminalQuiescence" {
            notice_seen |= frame["params"]["update"]["content"]["text"]
                .as_str()
                .is_some_and(|text| text.contains("notice seen"));
            return false;
        }
        true
    });
    assert!(
        notice_seen,
        "the settled child's notice turn drained inside the barrier: {terminal}"
    );
    assert_eq!(
        update_meta(&terminal)["quiescence"]["outstandingSubagents"],
        0,
        "the terminal reports a quiet family: {terminal}"
    );
    let (prompt_response, updates) = client.wait_response(prompt, TIMEOUT);
    assert!(
        updates.is_empty(),
        "the terminal frame is the last notification before the response: {updates:?}"
    );
    assert_eq!(
        prompt_response["result"],
        json!({ "stopReason": "end_turn" })
    );
}

/// A cancel during the settle cancels the outstanding subagents (TS
/// `cancelOutstandingRlmChildren` inside `stopSessionWork`): the prompt
/// answers cancelled once the stop sequence cancelled the held child, and
/// the roster reports the child cancelled. Close goes through the same
/// stop sequence, so it is not retested here.
#[test]
fn acp_cancel_during_settle_cancels_the_subagents() {
    let Some(kernel_python) = kernel_python() else {
        return;
    };
    let (mut client, session_id, active_session_id) =
        spawn_lane(&["--mode", "acp"], 120_000, &kernel_python);
    let socket = client.socket.clone();
    let prompt = client.request(
        "session/prompt",
        &json!({ "sessionId": session_id, "prompt": [{ "type": "text", "text": "spawn the kid" }] }),
    );
    // Readiness is the completion update with the held child outstanding:
    // the settle is provably waiting on it.
    client.wait_frame(TIMEOUT, |frame| {
        let meta = update_meta(frame);
        meta["phase"] == "event" && meta["quiescence"]["outstandingSubagents"] == 1
    });
    client.notify("session/cancel", &json!({ "sessionId": session_id }));
    let (prompt_response, _) = client.wait_response(prompt, TIMEOUT);
    assert_eq!(
        prompt_response["result"],
        json!({ "stopReason": "cancelled" }),
        "the cancel settles the prompt: {prompt_response}"
    );
    // The roster shows the child the stop sequence cancelled.
    let roster = daemon_request(
        &socket,
        "children",
        &json!({ "type": "get_rlm_children", "activeSessionId": active_session_id }),
    );
    let children = roster["data"]["children"]
        .as_array()
        .unwrap_or_else(|| panic!("a children roster: {roster}"))
        .clone();
    assert_eq!(children.len(), 1, "one spawned child: {children:?}");
    assert_eq!(
        children[0]["status"], "cancelled",
        "the stop cancelled the held child: {children:?}"
    );
}

/// EOF during the settle exits without waiting for the outstanding
/// subagents (TS aborts the controller and exits): the process is gone
/// while the resident session's held child still runs — EOF does not
/// cancel a resident session's children.
#[test]
fn acp_eof_during_settle_exits_and_leaves_resident_subagents() {
    let Some(kernel_python) = kernel_python() else {
        return;
    };
    let (mut client, session_id, active_session_id) =
        spawn_lane(&["--mode", "acp"], 120_000, &kernel_python);
    let socket = client.socket.clone();
    client.request(
        "session/prompt",
        &json!({ "sessionId": session_id, "prompt": [{ "type": "text", "text": "spawn the kid" }] }),
    );
    client.wait_frame(TIMEOUT, |frame| {
        let meta = update_meta(frame);
        meta["phase"] == "event" && meta["quiescence"]["outstandingSubagents"] == 1
    });
    client.close_stdin();
    assert!(client.child.wait().expect("the ACP child exits").success());
    // The resident session survives with the held child still running.
    let roster = daemon_request(
        &socket,
        "children",
        &json!({ "type": "get_rlm_children", "activeSessionId": active_session_id }),
    );
    let children = roster["data"]["children"]
        .as_array()
        .unwrap_or_else(|| panic!("a children roster: {roster}"))
        .clone();
    assert_eq!(children.len(), 1, "one spawned child: {children:?}");
    assert_eq!(
        children[0]["status"], "running",
        "EOF left the resident child running: {children:?}"
    );
}

/// A heartbeat change on the bound session broadcasts
/// `heartbeats_changed` to every client; the ACP link publishes the
/// change at origin turn 0 (connection-scoped like TS, never the active
/// prompt turn).
#[test]
fn acp_heartbeat_change_publishes_turn_zero_meta() {
    let mut client = AcpChild::spawn(
        &["--mode", "acp"],
        &json!({ "engine": "faux", "responses": ["The Nile."] }),
    );
    let socket = client.socket.clone();
    let _session_id = initialize_and_new_session(&mut client);
    let active_session_id = live_sessions(&socket)[0]["activeSessionId"].clone();
    let set = daemon_request(
        &socket,
        "heartbeat-set",
        &json!({
            "type": "heartbeat_set",
            "activeSessionId": active_session_id,
            "schedule": "every 90 seconds",
            "prompt": "check in",
        }),
    );
    assert_eq!(set["success"], true, "{set}");
    let change = client.wait_frame(TIMEOUT, |frame| {
        update_meta(frame)["heartbeatsChanged"] == json!(true)
    });
    assert_eq!(update_meta(&change)["promptTurnId"], 0, "{change}");
    assert_eq!(update_meta(&change)["phase"], "event", "{change}");
}

/// A bash run another client started on the bound session (the daemon's
/// `execute_bash`) surfaces as one synthetic tool call keyed by run id:
/// the started run, the streamed chunk, and the settled status.
#[test]
fn acp_user_bash_maps_to_a_synthetic_tool_call() {
    let mut client = AcpChild::spawn(
        &["--mode", "acp"],
        &json!({ "engine": "faux", "responses": ["The Nile."] }),
    );
    let socket = client.socket.clone();
    let _session_id = initialize_and_new_session(&mut client);
    let active_session_id = live_sessions(&socket)[0]["activeSessionId"].clone();
    let run = daemon_request(
        &socket,
        "bash",
        &json!({
            "type": "execute_bash",
            "activeSessionId": active_session_id,
            "command": "printf hi",
            "runId": "r1",
        }),
    );
    assert_eq!(run["success"], true, "{run}");
    let start = client.wait_frame(TIMEOUT, |frame| {
        frame["params"]["update"]["sessionUpdate"] == "tool_call"
    });
    assert_eq!(start["params"]["update"]["toolCallId"], "eukhe-bash-r1");
    assert_eq!(start["params"]["update"]["title"], "printf hi");
    assert_eq!(start["params"]["update"]["kind"], "execute");
    assert_eq!(
        start["params"]["update"]["rawInput"],
        json!({ "command": "printf hi" })
    );
    let output = client.wait_frame(TIMEOUT, |frame| {
        frame["params"]["update"]["sessionUpdate"] == "tool_call_update"
            && frame["params"]["update"]["toolCallId"] == "eukhe-bash-r1"
            && frame["params"]["update"]["status"] == "in_progress"
    });
    assert_eq!(
        output["params"]["update"]["content"][0]["content"]["text"], "hi",
        "{output}"
    );
    let end = client.wait_frame(TIMEOUT, |frame| {
        frame["params"]["update"]["sessionUpdate"] == "tool_call_update"
            && frame["params"]["update"]["toolCallId"] == "eukhe-bash-r1"
            && frame["params"]["update"]["status"] == "completed"
    });
    assert!(end["params"]["update"].get("content").is_none(), "{end}");
}
