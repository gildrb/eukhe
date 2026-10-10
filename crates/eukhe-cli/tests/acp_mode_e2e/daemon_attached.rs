//! Daemon-attached sessions: persistence and resume, EOF and close, cancel
//! races, failed turns, supervisor loss, compaction, goals, and autonomy.

use super::*;

#[test]
fn acp_daemon_attached_default_session_persists_and_resumes() {
    // Without --no-session the daemon session is saved and resident: it
    // survives the client's EOF, and --resume binds the same live worker.
    let home = tempfile::TempDir::new().unwrap();
    let home_path = home.path().to_path_buf();
    let socket = home_path.join("daemon.sock");
    std::fs::write(
        home_path.join("worker-script.json"),
        json!({ "engine": "faux", "responses": ["The Nile.", "Everest."] }).to_string(),
    )
    .unwrap();
    let child = daemon_attached_command(&home_path, &socket, &["--mode", "acp"])
        .env("DO_NOT_TRACK", "1")
        .spawn()
        .expect("binary present");
    let mut first = AcpChild::wrap(child, Some(home), socket.clone());
    let session_id = initialize_and_new_session(&mut first);
    assert_prompt_ends_turn(&mut first, &session_id, "Name a river.");

    let sessions = live_sessions(&socket);
    assert_eq!(sessions.len(), 1, "{sessions:?}");
    let active_session_id = sessions[0]["activeSessionId"].clone();
    // The durable storage is a directory (`<sessions>/<id>/`, pi-durable's
    // layout); its main transcript holds the turn.
    let session_file = sessions[0]["sessionFile"]
        .as_str()
        .unwrap_or_else(|| panic!("a saved session: {sessions:?}"))
        .to_string();
    assert!(
        std::path::Path::new(&session_file)
            .parent()
            .is_some_and(|dir| dir.ends_with(".eukhe/sessions")),
        "the session is saved in the session dir: {session_file}"
    );
    let texts =
        |dir: &str| durable_store::read_transcript(std::path::Path::new(dir)).message_texts();
    assert!(texts(&session_file)
        .iter()
        .any(|text| text == "Name a river."));
    let descriptor = worker_descriptor(&home_path);
    assert_eq!(descriptor["telemetryDisabled"], json!(true), "{descriptor}");
    assert!(
        descriptor.get("ownerClientId").is_none(),
        "a resident session has no owner: {descriptor}"
    );

    first.close_stdin();
    assert!(first.child.wait().expect("the ACP child exits").success());
    let sessions = live_sessions(&socket);
    assert_eq!(
        sessions.len(),
        1,
        "a resident session survives EOF: {sessions:?}"
    );
    assert_eq!(sessions[0]["activeSessionId"], active_session_id);

    // A relative `--resume` selector resolves against the CLI's working
    // directory: the agent dir here, not the stored session cwd.
    let file_name = std::path::Path::new(&session_file)
        .file_name()
        .and_then(std::ffi::OsStr::to_str)
        .expect("a session file name");
    let agent_dir = std::path::Path::new(&session_file)
        .parent()
        .and_then(std::path::Path::parent)
        .expect("the agent dir holding the session dir");
    let child = daemon_attached_command(
        &home_path,
        &socket,
        &[
            "--mode",
            "acp",
            "--resume",
            &format!("sessions/{file_name}"),
        ],
    )
    .current_dir(agent_dir)
    .spawn()
    .expect("binary present");
    let mut second = AcpChild::wrap(child, None, socket.clone());
    let session_id = initialize_and_new_session(&mut second);
    assert_prompt_ends_turn(&mut second, &session_id, "Name a mountain.");
    let sessions = live_sessions(&socket);
    assert_eq!(sessions.len(), 1, "{sessions:?}");
    assert_eq!(
        sessions[0]["activeSessionId"], active_session_id,
        "--resume binds the live worker"
    );
    let saved = texts(&session_file);
    assert!(
        saved.iter().any(|text| text == "Name a river.")
            && saved.iter().any(|text| text == "Name a mountain."),
        "{saved:?}"
    );
}

#[test]
fn acp_daemon_attached_resident_eof_mid_turn_cancels_the_prompt() {
    let answer = "a paced answer that streams slowly enough to close mid-turn";
    let mut client = AcpChild::spawn(
        &["--mode", "acp"],
        &json!({ "engine": "faux", "tokensPerSecond": 2, "responses": [{ "text": answer }] }),
    );
    let socket = client.socket.clone();
    let session_id = initialize_and_new_session(&mut client);
    let _ = client.request(
        "session/prompt",
        &json!({ "sessionId": session_id, "prompt": [{ "type": "text", "text": "a slow question" }] }),
    );
    client.wait_update("agent_message_chunk", TIMEOUT);
    let session = live_sessions(&socket).remove(0);
    let active_session_id = session["activeSessionId"].clone();
    let session_dir = session["sessionFile"]
        .as_str()
        .unwrap_or_else(|| panic!("a saved session: {session}"))
        .to_string();

    client.close_stdin();
    assert!(client.child.wait().expect("the ACP child exits").success());
    let idle = daemon_request(
        &socket,
        "idle",
        &json!({ "type": "wait_for_idle", "activeSessionId": active_session_id }),
    );
    assert_eq!(idle["success"], true, "{idle}");
    let sessions = live_sessions(&socket);
    assert_eq!(
        sessions.len(),
        1,
        "a resident session survives EOF: {sessions:?}"
    );
    assert_eq!(sessions[0]["activeSessionId"], active_session_id);
    // The durable storage is a directory: its main transcript holds the
    // prompt and no answer.
    let saved = durable_store::read_transcript(std::path::Path::new(&session_dir)).message_texts();
    assert!(
        saved.iter().any(|text| text == "a slow question"),
        "{saved:?}"
    );
    assert!(
        !saved.iter().any(|text| text.contains(answer)),
        "the EOF cancelled the running prompt: {saved:?}"
    );
}

/// EOF while `session/new` is still running: the reader awaits the
/// handler before it reads further, so the teardown at EOF releases the
/// session it installs and the process exits.
#[test]
fn acp_daemon_attached_eof_during_session_new_exits() {
    let mut client = AcpChild::spawn(
        &["--mode", "acp"],
        &json!({ "engine": "faux", "responses": ["The Nile."] }),
    );
    let init = client.request("initialize", &initialize_params());
    let _ = client.wait_response(init, TIMEOUT);
    let new = client.request("session/new", &json!({ "mcpServers": [] }));
    client.close_stdin();
    let (new_response, _) = client.wait_response(new, TIMEOUT);
    assert!(
        new_response["result"]["sessionId"].is_string(),
        "session/new answers: {new_response}"
    );
    assert!(client.child.wait().expect("the ACP child exits").success());
}

#[test]
fn acp_daemon_attached_close_keeps_the_worker_and_new_rebinds_it() {
    let mut client = AcpChild::spawn(
        &["--mode", "acp", "--no-session"],
        &json!({ "engine": "faux", "responses": ["The Nile.", "Everest."] }),
    );
    let socket = client.socket.clone();
    let first = initialize_and_new_session(&mut client);
    let wrong = client.request("session/close", &json!({ "sessionId": "not-the-session" }));
    let (wrong_response, _) = client.wait_response(wrong, TIMEOUT);
    assert_eq!(
        wrong_response["error"]["data"]["details"], "Unknown ACP session: not-the-session",
        "{wrong_response}"
    );
    assert_prompt_ends_turn(&mut client, &first, "Name a river.");
    let active_session_id = live_sessions(&socket)[0]["activeSessionId"].clone();
    let descriptor = worker_descriptor(socket.parent().unwrap());
    let owner = json!(format!("acp:{}", client.child.id()));
    assert_eq!(descriptor["ownerClientId"], owner, "{descriptor}");

    let close = client.request("session/close", &json!({ "sessionId": first }));
    let (close_response, _) = client.wait_response(close, TIMEOUT);
    assert_eq!(close_response["result"], json!({}));
    let sessions = live_sessions(&socket);
    assert_eq!(sessions.len(), 1, "close keeps the worker: {sessions:?}");
    assert_eq!(sessions[0]["activeSessionId"], active_session_id);

    let second = new_session(&mut client);
    assert_ne!(second, first);
    let updates = assert_prompt_ends_turn(&mut client, &second, "Name a mountain.");
    let chunk = updates
        .iter()
        .find(|update| update["params"]["update"]["sessionUpdate"] == "agent_message_chunk")
        .expect("a message chunk");
    // The event mapping restarts with the session, like TS.
    assert_eq!(chunk["params"]["update"]["messageId"], "eukhe-assistant-1");
    let sessions = live_sessions(&socket);
    assert_eq!(sessions.len(), 1, "{sessions:?}");
    assert_eq!(
        sessions[0]["activeSessionId"], active_session_id,
        "session/new binds the same daemon session"
    );
}

#[test]
fn acp_daemon_attached_prompt_during_cancel_is_refused() {
    // A prompt behind a cancel is refused while the stop runs, and the
    // cancelled response comes after the stop, so a resend right after it
    // runs.
    let mut client = AcpChild::spawn(
        &["--mode", "acp", "--no-session"],
        &json!({ "engine": "faux", "tokensPerSecond": 2, "responses": [
            { "text": "a paced answer that streams slowly enough to cancel mid-turn" },
            "AFTER-STOP",
        ] }),
    );
    let init = client.request("initialize", &initialize_params());
    let _ = client.wait_response(init, TIMEOUT);
    let new = client.request("session/new", &json!({ "mcpServers": [] }));
    let (new_response, _) = client.wait_response(new, TIMEOUT);
    let session_id = new_response["result"]["sessionId"]
        .as_str()
        .unwrap()
        .to_string();
    let first = client.request(
        "session/prompt",
        &json!({ "sessionId": session_id, "prompt": [{ "type": "text", "text": "a slow question" }] }),
    );
    client.wait_update("agent_message_chunk", TIMEOUT);
    client.notify("session/cancel", &json!({ "sessionId": session_id }));
    let second = client.request(
        "session/prompt",
        &json!({ "sessionId": session_id, "prompt": [{ "type": "text", "text": "behind the stop" }] }),
    );
    let (second_response, _) = client.wait_response(second, TIMEOUT);
    assert_eq!(
        second_response["error"]["code"], -32603,
        "the prompt behind the cancel is refused: {second_response}"
    );
    assert_eq!(
        second_response["error"]["data"]["details"],
        format!("ACP session is cancelling: {session_id}"),
        "the refusal names the cancelling window: {second_response}"
    );
    let (first_response, _) = client.wait_response(first, TIMEOUT);
    assert_eq!(
        first_response["result"]["stopReason"], "cancelled",
        "the cancel settles the running turn: {first_response}"
    );
    // The resend also resumes the queued-input admission the cancel
    // suspended (TS sends `followUp` + `queueIfBusy: true`).
    let third = client.request(
        "session/prompt",
        &json!({ "sessionId": session_id, "prompt": [{ "type": "text", "text": "the resend" }] }),
    );
    let (third_response, updates) = client.wait_response(third, TIMEOUT);
    assert_eq!(
        third_response["result"]["stopReason"], "end_turn",
        "the stop cleared before the cancelled response: {third_response}"
    );
    let chunk = updates
        .iter()
        .find(|update| update["params"]["update"]["sessionUpdate"] == "agent_message_chunk")
        .expect("the resent turn streams its scripted answer");
    assert_eq!(
        chunk["params"]["update"]["content"],
        json!({ "type": "text", "text": "AFTER-STOP" })
    );
}

#[test]
fn acp_daemon_attached_failed_turn_publishes_only_the_error_boundary() {
    // A failed turn (here: the empty-prompt rejection) publishes one
    // error boundary and no terminal-quiescence update (TS settle catch).
    let mut client = AcpChild::spawn(
        &["--mode", "acp", "--no-session"],
        &json!({ "engine": "faux", "responses": [] }),
    );
    let init = client.request("initialize", &initialize_params());
    let _ = client.wait_response(init, TIMEOUT);
    let new = client.request("session/new", &json!({ "mcpServers": [] }));
    let (new_response, _) = client.wait_response(new, TIMEOUT);
    let session_id = new_response["result"]["sessionId"]
        .as_str()
        .unwrap()
        .to_string();
    let prompt = client.request(
        "session/prompt",
        &json!({ "sessionId": session_id, "prompt": [] }),
    );
    let (prompt_response, updates) = client.wait_response(prompt, TIMEOUT);
    assert_eq!(
        prompt_response["error"]["code"], -32603,
        "the failed turn errors the request: {prompt_response}"
    );
    assert!(
        prompt_response["error"]["data"]["details"]
            .as_str()
            .unwrap_or_default()
            .contains("Prompt cannot be empty"),
        "the worker's failure is the error: {prompt_response}"
    );
    let mut boundaries = 0;
    for update in &updates {
        let body = &update["params"]["update"];
        let meta = &body["_meta"]["com.eukhe"];
        assert_ne!(
            meta["phase"], "terminalQuiescence",
            "a failed turn never publishes a terminal frame: {updates:?}"
        );
        if meta["phase"] == "responseBoundary" {
            boundaries += 1;
            assert_eq!(
                meta["terminalQuiescenceExpected"], false,
                "the one boundary declares no terminal expectation: {updates:?}"
            );
            assert_eq!(meta["outcome"], "error");
        }
    }
    assert_eq!(
        boundaries, 1,
        "the failed turn published exactly one correlated error boundary: {updates:?}"
    );
}

#[test]
fn acp_daemon_attached_supervisor_loss_fails_the_prompt() {
    // The supervisor dies while a prompt is in flight: the pending
    // request must fail fast with an error response, never hang, because
    // the link close is the turn's liveness bound (turn-long requests
    // carry no timer).
    let mut client = AcpChild::spawn(
        &["--mode", "acp", "--no-session"],
        &json!({ "engine": "faux", "tokensPerSecond": 2, "responses": [
            { "text": "a paced answer that streams slowly enough to outlive the supervisor" },
        ] }),
    );
    let socket = client.socket.clone();
    let init = client.request("initialize", &initialize_params());
    let _ = client.wait_response(init, TIMEOUT);
    let new = client.request("session/new", &json!({ "mcpServers": [] }));
    let (new_response, _) = client.wait_response(new, TIMEOUT);
    let session_id = new_response["result"]["sessionId"]
        .as_str()
        .unwrap()
        .to_string();
    let prompt = client.request(
        "session/prompt",
        &json!({ "sessionId": session_id, "prompt": [{ "type": "text", "text": "a slow question" }] }),
    );
    // Readiness is the turn's own first streamed chunk: the prompt is
    // provably in flight before the supervisor goes away.
    client.wait_update("agent_message_chunk", TIMEOUT);
    // Crash the supervisor (no graceful drain, so the in-flight response
    // can never arrive). Its pid comes from the hello frame every new
    // connection receives.
    let probe = eukhe_types::platform::transport::connect_blocking(&socket).expect("daemon socket");
    let reader = probe.try_clone_box().expect("daemon socket clone");
    let _ = reader.set_read_timeout(Duration::from_mins(2));
    let hello = BufReader::new(reader)
        .lines()
        .map(|line| {
            serde_json::from_str::<Value>(&line.expect("daemon line")).expect("daemon JSON")
        })
        .find(|frame| frame["type"] == json!("daemon_hello"))
        .expect("the daemon closed without a hello");
    let pid = hello["supervisorPid"].as_u64().expect("supervisor pid");
    drop(probe);
    let killed = std::process::Command::new("kill")
        .args(["-9", &pid.to_string()])
        .status()
        .expect("kill the supervisor");
    assert!(killed.success(), "the supervisor crash did not run");
    let (prompt_response, _) = client.wait_response(prompt, TIMEOUT);
    assert_eq!(
        prompt_response["error"],
        json!({
            "code": -32603,
            "message": "Internal error",
            "data": { "details": "the daemon connection closed mid-request" }
        }),
        "the in-flight prompt fails fast on supervisor loss: {prompt_response}"
    );
}

#[test]
fn acp_daemon_attached_image_only_prompt_reaches_the_session() {
    let mut client = AcpChild::spawn(
        &["--mode", "acp", "--no-session"],
        &json!({ "engine": "faux", "responses": ["SAW-IMAGE"] }),
    );
    let socket = client.socket.clone();
    let init = client.request("initialize", &initialize_params());
    let _ = client.wait_response(init, TIMEOUT);
    let new = client.request("session/new", &json!({ "mcpServers": [] }));
    let (new_response, _) = client.wait_response(new, TIMEOUT);
    let session_id = new_response["result"]["sessionId"]
        .as_str()
        .unwrap()
        .to_string();
    // 1x1 PNG
    let png = "iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVR42mP8z8BQDwAEhQGAhKmMIQAAAABJRU5ErkJggg==";
    let prompt = client.request(
        "session/prompt",
        &json!({
            "sessionId": session_id,
            "prompt": [
                { "type": "image", "data": png, "mimeType": "image/png" },
            ],
        }),
    );
    let (prompt_response, _) = client.wait_response(prompt, TIMEOUT);
    assert_eq!(
        prompt_response["result"]["stopReason"], "end_turn",
        "an image-only prompt runs a turn: {prompt_response}"
    );
    // The stored user row carries the image: an empty text block first,
    // then the images (TS `_buildPromptContent`).
    let list = daemon_request(&socket, "img-list", &json!({ "type": "list" }));
    let active_session_id = &list["data"]["sessions"][0]["activeSessionId"];
    let messages = daemon_request(
        &socket,
        "img-msgs",
        &json!({ "type": "get_messages", "activeSessionId": active_session_id }),
    );
    let user = messages["data"]["messages"]
        .as_array()
        .unwrap()
        .iter()
        .find(|m| m["role"] == "user")
        .unwrap();
    assert_eq!(
        user["content"],
        json!([
            { "type": "text", "text": "" },
            { "type": "image", "data": png, "mimeType": "image/png" },
        ])
    );
}

#[test]
fn acp_compact_command_publishes_the_compaction_meta_and_end_turn() {
    // The faux session is short, so `/compact` skips (TS
    // `CompactionSkippedError`): the observable parity is the
    // `compaction: {}` namespaced update and the normal end_turn response.
    let script = json!({ "engine": "faux", "responses": ["one answer"] });
    let mut client = AcpChild::spawn(&["--mode", "acp", "--no-session"], &script);
    let init = client.request("initialize", &initialize_params());
    let _ = client.wait_response(init, TIMEOUT);
    let new = client.request("session/new", &json!({ "mcpServers": [] }));
    let (new_response, _) = client.wait_response(new, TIMEOUT);
    let session_id = new_response["result"]["sessionId"]
        .as_str()
        .unwrap()
        .to_string();

    let prompt = client.request(
        "session/prompt",
        &json!({ "sessionId": session_id, "prompt": [{ "type": "text", "text": "/compact" }] }),
    );
    let (prompt_response, updates) = client.wait_response(prompt, TIMEOUT);

    let compaction = updates
        .iter()
        .find(|update| {
            let meta = &update["params"]["update"]["_meta"]["com.eukhe"];
            meta.get("compaction").is_some_and(|value| !value.is_null())
        })
        .expect("a compaction meta frame");
    let meta = &compaction["params"]["update"]["_meta"]["com.eukhe"];
    assert_eq!(
        meta["compaction"],
        json!({}),
        "a skipped compaction publishes the empty payload"
    );
    assert_eq!(meta["phase"], "event");

    // The turn settles normally: boundary, completion, terminal, end_turn.
    let boundary = updates.iter().any(|update| {
        let meta = &update["params"]["update"]["_meta"]["com.eukhe"];
        meta["phase"] == "responseBoundary" && meta["terminalQuiescenceExpected"] == true
    });
    assert!(boundary, "updates: {updates:?}");
    assert_eq!(
        prompt_response["result"],
        json!({ "stopReason": "end_turn" })
    );
}

#[test]
fn acp_goal_command_publishes_goal_meta_and_runs_the_continuation() {
    // `/goal` start schedules its continuation as the turn's model segment:
    // the goal meta frame precedes the streamed answer, and the usage
    // accounting publishes a second goal frame after the message settles.
    // The tiny budget bounds the goal loop the worker turn loop
    // hosts (TS parity: the continuation loop runs inside the same
    // session/prompt request): the crossing turn's budget-limit steer is
    // the second model segment, and the budget_limited goal settles the
    // prompt with end_turn instead of looping forever.
    let script = json!({ "engine": "faux", "responses": ["GOAL-PROGRESS", "WRAP-UP"] });
    let mut client = AcpChild::spawn(&["--mode", "acp", "--no-session"], &script);
    let init = client.request("initialize", &initialize_params());
    let _ = client.wait_response(init, TIMEOUT);
    let new = client.request("session/new", &json!({ "mcpServers": [] }));
    let (new_response, _) = client.wait_response(new, TIMEOUT);
    let session_id = new_response["result"]["sessionId"]
        .as_str()
        .unwrap()
        .to_string();

    let prompt = client.request(
        "session/prompt",
        &json!({ "sessionId": session_id, "prompt": [{ "type": "text", "text": "/goal --budget 5 reply with exactly: GOAL-PROGRESS" }] }),
    );
    let (prompt_response, updates) = client.wait_response(prompt, TIMEOUT);

    let goal_frames: Vec<&Value> = updates
        .iter()
        .filter(|update| {
            let meta = &update["params"]["update"]["_meta"]["com.eukhe"];
            meta.get("goal").is_some_and(|value| !value.is_null())
        })
        .collect();
    assert!(!goal_frames.is_empty(), "updates: {updates:?}");
    let first = &goal_frames[0]["params"]["update"]["_meta"]["com.eukhe"]["goal"];
    assert_eq!(first["status"], "active");
    assert_eq!(first["objective"], "reply with exactly: GOAL-PROGRESS");
    assert_eq!(first["tokenBudget"], 5);
    assert_eq!(first["tokensUsed"], 0);
    // A usage update follows the settled message: the tiny budget
    // crosses at the first turn, so the goal is budget_limited before
    // the wrap-up steer segment runs.
    assert!(goal_frames.len() >= 2, "goal frames: {goal_frames:?}");
    let second = &goal_frames[1]["params"]["update"]["_meta"]["com.eukhe"]["goal"];
    assert_eq!(second["status"], "budget_limited");
    assert!(second["tokensUsed"].as_u64().unwrap_or(0) > 0);
    // The budget-limit wrap-up steer ran as the prompt's second model
    // segment (its streamed answer is the second scripted response; the
    // faux pacing may split one answer into chunks, so the joined text
    // carries the observable contract).
    let streamed: String = updates
        .iter()
        .filter_map(|update| update["params"]["update"]["content"]["text"].as_str())
        .collect();
    assert!(streamed.contains("GOAL-PROGRESS"), "updates: {updates:?}");
    assert!(streamed.contains("WRAP-UP"), "updates: {updates:?}");
    assert_eq!(
        prompt_response["result"],
        json!({ "stopReason": "end_turn" })
    );
}

#[test]
fn acp_autonomous_token_limit_maps_to_max_tokens_stop_reason() {
    // A one-token budget is exhausted by the first turn: the driver stops
    // with the token limit, the completion envelope carries the autonomous
    // accounting, and the stop reason is `max_tokens`.
    let script = json!({ "engine": "faux", "responses": ["an answer"] });
    let mut client = AcpChild::spawn(
        &[
            "--mode",
            "acp",
            "--no-session",
            "--autonomous",
            "--autonomous-max-tokens",
            "1",
        ],
        &script,
    );
    let init = client.request("initialize", &initialize_params());
    let _ = client.wait_response(init, TIMEOUT);
    let new = client.request("session/new", &json!({ "mcpServers": [] }));
    let (new_response, _) = client.wait_response(new, TIMEOUT);
    let session_id = new_response["result"]["sessionId"]
        .as_str()
        .unwrap()
        .to_string();

    let prompt = client.request(
        "session/prompt",
        &json!({ "sessionId": session_id, "prompt": [{ "type": "text", "text": "do the thing" }] }),
    );
    let (prompt_response, updates) = client.wait_response(prompt, TIMEOUT);

    let completion = updates
        .iter()
        .find(|update| {
            let meta = &update["params"]["update"]["_meta"]["com.eukhe"];
            meta["phase"] == "event" && meta.get("autonomous").is_some_and(|v| !v.is_null())
        })
        .expect("an autonomous completion meta");
    let autonomous = &completion["params"]["update"]["_meta"]["com.eukhe"]["autonomous"];
    assert_eq!(autonomous["enabled"], true);
    assert_eq!(autonomous["turnsUsed"], 1);
    let quiescence = &completion["params"]["update"]["_meta"]["com.eukhe"]["quiescence"];
    assert_eq!(quiescence["outstandingSubagents"], 0);

    assert_eq!(
        prompt_response["result"],
        json!({ "stopReason": "max_tokens" })
    );
}

#[test]
fn acp_autonomous_disabled_reports_end_turn_without_accounting() {
    // Without autonomous flags the completion envelope carries no autonomous
    // meta and the stop reason is end_turn.
    let script = json!({ "engine": "faux", "responses": ["an answer"] });
    let mut client = AcpChild::spawn(&["--mode", "acp", "--no-session"], &script);
    let init = client.request("initialize", &initialize_params());
    let _ = client.wait_response(init, TIMEOUT);
    let new = client.request("session/new", &json!({ "mcpServers": [] }));
    let (new_response, _) = client.wait_response(new, TIMEOUT);
    let session_id = new_response["result"]["sessionId"]
        .as_str()
        .unwrap()
        .to_string();

    let prompt = client.request(
        "session/prompt",
        &json!({ "sessionId": session_id, "prompt": [{ "type": "text", "text": "hi" }] }),
    );
    let (prompt_response, updates) = client.wait_response(prompt, TIMEOUT);
    for update in &updates {
        let meta = &update["params"]["update"]["_meta"]["com.eukhe"];
        assert!(
            meta.get("autonomous")
                .is_none_or(serde_json::Value::is_null),
            "no autonomous meta"
        );
    }
    assert_eq!(
        prompt_response["result"],
        json!({ "stopReason": "end_turn" })
    );
}

#[test]
fn acp_daemon_attached_reports_autonomous_accounting_and_limit_stop_reason() {
    // An autonomous run with --max-turns 1: the completion envelope carries
    // the _meta.autonomous accounting (TS waitForHeadlessCompletion), the
    // quiescence observation counts the remaining continuations, and the
    // turn limit surfaces as max_turn_requests (TS acpStopReason).
    let mut client = AcpChild::spawn(
        &["--mode", "acp", "--no-session"],
        &json!({ "engine": "faux", "responses": [
            "enabling the run",
            "one turn runs, then the limit stops the run",
        ] }),
    );
    let init = client.request("initialize", &initialize_params());
    let _ = client.wait_response(init, TIMEOUT);
    let new = client.request("session/new", &json!({ "mcpServers": [] }));
    let (new_response, _) = client.wait_response(new, Duration::from_mins(1));
    assert!(
        new_response["result"]["sessionId"].is_string(),
        "daemon-attached admission succeeds: {new_response}"
    );
    let session_id = new_response["result"]["sessionId"]
        .as_str()
        .unwrap()
        .to_string();
    // Turn on the run with a one-turn budget.
    let enable = client.request(
        "session/prompt",
        &json!({
            "sessionId": session_id,
            "prompt": [{ "type": "text", "text": "/autonomous on --max-turns 1" }],
        }),
    );
    let (enable_response, updates) = client.wait_response(enable, Duration::from_mins(2));
    assert_eq!(enable_response["result"]["stopReason"], "end_turn");
    // The enabled accounting is already visible on the command turn's
    // completion envelope (the headless-completion status of the run).
    let enabled_meta = updates.iter().find_map(|update| {
        let meta = &update["params"]["update"]["_meta"]["com.eukhe"]["autonomous"];
        (!meta.is_null()).then(|| meta.clone())
    });
    let enabled_meta = enabled_meta.expect("the enabled run's accounting reached the surface");
    assert_eq!(enabled_meta["enabled"], true);
    // The model turn: one turn runs, the max-turns limit stops the run.
    let prompt = client.request(
        "session/prompt",
        &json!({
            "sessionId": session_id,
            "prompt": [{ "type": "text", "text": "say something" }],
        }),
    );
    let (prompt_response, updates) = client.wait_response(prompt, Duration::from_mins(2));
    assert_eq!(
        prompt_response["result"],
        json!({ "stopReason": "max_turn_requests" }),
        "the turn limit maps to the TS stop reason: {prompt_response}"
    );
    let accounted = updates.iter().find_map(|update| {
        let meta = &update["params"]["update"]["_meta"]["com.eukhe"]["autonomous"];
        (meta["enabled"] == json!(true) && meta["turnsUsed"] == json!(1)).then(|| meta.clone())
    });
    let accounted = accounted.expect("the limited turn's accounting reached the surface");
    assert_eq!(accounted["continuationsUsed"], 0);
    // The quiescence observation subtracts the run's own limits (TS
    // quiescenceMeta): the named budget flag `--max-turns 1` makes the
    // unnamed limits the JSON-safe unlimited sentinel (TS
    // parseAutonomousCommand budget fill), so the remaining continuation
    // slots are that sentinel minus the zero the stopped run consumed.
    let remaining = updates.iter().find_map(|update| {
        let quiescence = &update["params"]["update"]["_meta"]["com.eukhe"]["quiescence"];
        (!quiescence.is_null()).then(|| quiescence["remainingAutonomousContinuations"].clone())
    });
    assert_eq!(
        remaining,
        Some(json!(9_007_199_254_740_991u64)),
        "the run's unlimited continuation budget minus used"
    );
    let close = client.request("session/close", &json!({ "sessionId": session_id }));
    let (close_response, _) = client.wait_response(close, Duration::from_mins(1));
    assert_eq!(close_response["result"], json!({}));
    drop(client);
}
