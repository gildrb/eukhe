//! Session close and stop fencing on the daemon-attached path: the
//! per-connection MCP owner release, the unreachable-daemon exit, the
//! stop-failure fence, the close's input pause, and the per-turn stop
//! reason.

use super::*;

fn probe_acp_mcp_servers(socket: &std::path::Path, active_session_id: &str) -> Value {
    daemon_request(
        socket,
        "acp-mcp-replace",
        &json!({
            "type": "replace_acp_mcp_servers",
            "activeSessionId": active_session_id,
            "ownerId": "acp-e2e-probe",
            "servers": [{
                "type": "http",
                "name": "probe",
                "url": "https://mcp.invalid/probe",
                "headers": {},
            }],
        }),
    )
}

/// The first live daemon session, polled until the supervisor lists it.
fn wait_live_session(socket: &std::path::Path) -> Value {
    let deadline = Instant::now() + TIMEOUT;
    loop {
        let sessions = live_sessions(socket);
        if let Some(session) = sessions.first() {
            return session.clone();
        }
        let timeout_left = deadline.saturating_duration_since(Instant::now());
        assert!(
            !timeout_left.is_zero(),
            "no daemon session ever registered on {}",
            socket.display()
        );
        std::thread::sleep(Duration::from_millis(50));
    }
}

#[test]
fn acp_daemon_attached_close_clears_the_connection_mcp_servers() {
    let script = json!({ "engine": "faux", "responses": ["unused"] });
    let mut client = AcpChild::spawn(&["--mode", "acp", "--no-session"], &script);
    let socket = client.socket.clone();
    let init = client.request("initialize", &initialize_params());
    let _ = client.wait_response(init, TIMEOUT);
    let new = client.request(
        "session/new",
        &json!({ "mcpServers": [
            { "name": "close-clear", "type": "http", "url": "https://mcp.invalid/close-clear", "headers": [] },
        ]}),
    );
    let (new_response, _) = client.wait_response(new, TIMEOUT);
    let session_id = new_response["result"]["sessionId"]
        .as_str()
        .expect("admission succeeds")
        .to_string();
    let active_session_id = wait_live_session(&socket)["activeSessionId"]
        .as_str()
        .expect("the daemon session id")
        .to_string();
    let owned = probe_acp_mcp_servers(&socket, &active_session_id);
    assert_eq!(
        owned["success"], false,
        "the open session owns its admitted servers: {owned}"
    );
    assert_eq!(
        owned["error"],
        "ACP MCP configuration is owned by another client"
    );
    let close = client.request("session/close", &json!({ "sessionId": session_id }));
    let (close_response, _) = client.wait_response(close, TIMEOUT);
    assert_eq!(close_response["result"], json!({}));
    let released = probe_acp_mcp_servers(&socket, &active_session_id);
    assert_eq!(
        released["success"], true,
        "session/close released the connection's servers: {released}"
    );
}

#[test]
fn acp_daemon_attached_eof_teardown_clears_the_connection_mcp_servers() {
    let script = json!({ "engine": "faux", "responses": ["unused"] });
    let mut client = AcpChild::spawn(&["--mode", "acp"], &script);
    let socket = client.socket.clone();
    let init = client.request("initialize", &initialize_params());
    let _ = client.wait_response(init, TIMEOUT);
    let new = client.request(
        "session/new",
        &json!({ "mcpServers": [
            { "name": "eof-clear", "type": "http", "url": "https://mcp.invalid/eof-clear", "headers": [] },
        ]}),
    );
    let (new_response, _) = client.wait_response(new, TIMEOUT);
    assert!(
        new_response["result"]["sessionId"].is_string(),
        "admission succeeds: {new_response}"
    );
    let active_session_id = wait_live_session(&socket)["activeSessionId"]
        .as_str()
        .expect("the daemon session id")
        .to_string();
    let owned = probe_acp_mcp_servers(&socket, &active_session_id);
    assert_eq!(
        owned["success"], false,
        "the open session owns its admitted servers: {owned}"
    );
    client.close_stdin();
    assert!(client.child.wait().expect("the ACP child exits").success());
    let released = probe_acp_mcp_servers(&socket, &active_session_id);
    assert_eq!(
        released["success"], true,
        "the EOF teardown released the connection's servers: {released}"
    );
}

#[test]
fn acp_mode_daemon_unreachable_exits_1_without_fallback() {
    let home = tempfile::TempDir::new().unwrap();
    let socket = home.path().join("daemon.sock");
    std::fs::write(&socket, "not a socket").unwrap();
    std::fs::write(
        home.path().join("worker-script.json"),
        json!({ "engine": "faux", "responses": ["unused"] }).to_string(),
    )
    .unwrap();
    let output = daemon_attached_command(home.path(), &socket, &["--mode", "acp", "--no-session"])
        .output()
        .expect("binary present");
    assert_eq!(
        output.status.code(),
        Some(1),
        "exit 1: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        output.stdout.is_empty(),
        "no ACP frames on stdout: {}",
        String::from_utf8_lossy(&output.stdout)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("Error: "),
        "the startup failure is an error line: {stderr}"
    );
    assert!(
        stderr.contains("Timed out waiting for the Eukhe daemon to start"),
        "the daemon never became reachable: {stderr}"
    );
}

#[cfg(unix)]
#[test]
fn acp_daemon_attached_close_stop_failure_fences_the_session() {
    let mut client = AcpChild::spawn(
        &["--mode", "acp", "--no-session"],
        &json!({ "engine": "faux", "responses": ["unused"] }),
    );
    let session_id = initialize_and_new_session(&mut client);
    let probe =
        eukhe_types::platform::transport::connect_blocking(&client.socket).expect("daemon socket");
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

    let close = client.request("session/close", &json!({ "sessionId": session_id }));
    let (close_response, _) = client.wait_response(close, TIMEOUT);
    assert_eq!(
        close_response["error"]["code"], -32603,
        "the failed stop errors the close: {close_response}"
    );
    let stop_failure = close_response["error"]["data"]["details"]
        .as_str()
        .unwrap_or_default()
        .to_string();
    assert!(
        stop_failure.contains("the daemon connection"),
        "the stop error is the fence's message: {stop_failure}"
    );

    let prompt = client.request(
        "session/prompt",
        &json!({ "sessionId": session_id, "prompt": [{ "type": "text", "text": "after the failed stop" }] }),
    );
    let (prompt_response, _) = client.wait_response(prompt, TIMEOUT);
    assert_eq!(
        prompt_response["error"]["data"]["details"],
        format!("ACP session stop failed: {stop_failure}"),
        "a prompt while the stop failed answers the TS fence: {prompt_response}"
    );

    let refused = client.request("session/new", &json!({ "mcpServers": [] }));
    let (refused_response, _) = client.wait_response(refused, TIMEOUT);
    assert_eq!(
        refused_response["error"]["data"]["details"],
        "eukhe ACP mode hosts one session per connection; start another eukhe process for a second session",
        "the close-failed session keeps the single-session slot: {refused_response}"
    );

    let close_again = client.request("session/close", &json!({ "sessionId": session_id }));
    let (again_response, _) = client.wait_response(close_again, TIMEOUT);
    assert_eq!(again_response["error"]["code"], -32603);
    assert_ne!(
        again_response["error"]["data"]["details"],
        format!("Unknown ACP session: {session_id}"),
        "the session stays bound after the failed close: {again_response}"
    );
    drop(client);
}

#[test]
fn acp_daemon_attached_close_holds_the_input_pause_until_the_next_session_new() {
    let mut client = AcpChild::spawn(
        &["--mode", "acp", "--no-session"],
        &json!({ "engine": "faux", "responses": ["first", { "text": "FOREIGN", "delayMs": 150_000 }] }),
    );
    let socket = client.socket.clone();
    let session_id = initialize_and_new_session(&mut client);
    assert_prompt_ends_turn(&mut client, &session_id, "one");

    let close = client.request("session/close", &json!({ "sessionId": session_id }));
    let (close_response, _) = client.wait_response(close, TIMEOUT);
    assert_eq!(close_response["result"], json!({}));

    let active_session_id = live_sessions(&socket)[0]["activeSessionId"]
        .as_str()
        .expect("the resident session")
        .to_string();
    let _ = daemon_request(
        &socket,
        "foreign-follow-up",
        &json!({ "type": "follow_up", "activeSessionId": active_session_id, "message": "foreign" }),
    );
    let idle = daemon_request(
        &socket,
        "foreign-idle",
        &json!({ "type": "wait_for_idle", "activeSessionId": active_session_id }),
    );
    assert!(
        idle["success"] == json!(true),
        "no foreign turn runs on the resident session while the close holds the input pause: {idle}"
    );

    let _second = new_session(&mut client);
    drop(client);
}

#[test]
fn acp_truncated_final_response_maps_to_max_tokens_stop_reason() {
    // A turn whose final assistant message stopped at the provider's
    // output-token cap resolves with max_tokens, not end_turn; and the
    // stop reason is per-turn — the following /compact prompt runs no
    // model call (the faux session is short, so it skips), so it must not
    // inherit the truncated turn's length.
    let script = json!({
        "engine": "faux",
        "responses": [{ "text": "half an answer", "stopReason": "length" }],
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

    let prompt = client.request(
        "session/prompt",
        &json!({ "sessionId": session_id, "prompt": [{ "type": "text", "text": "write a long essay" }] }),
    );
    let (prompt_response, _) = client.wait_response(prompt, TIMEOUT);
    assert_eq!(
        prompt_response["result"],
        json!({ "stopReason": "max_tokens" })
    );

    let slash = client.request(
        "session/prompt",
        &json!({ "sessionId": session_id, "prompt": [{ "type": "text", "text": "/compact" }] }),
    );
    let (slash_response, _) = client.wait_response(slash, TIMEOUT);
    assert_eq!(
        slash_response["result"],
        json!({ "stopReason": "end_turn" })
    );
}
