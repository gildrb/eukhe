//! The ACP protocol surface: initialize, prompt streaming, error shapes,
//! MCP admission, and the daemon-attached cancel and close paths.

use super::*;

/// The TS initialize response shape (capture `ts-happy_path.jsonl`), with the
/// version and sessionId-class fields normalized as volatile.
#[test]
fn acp_initialize_matches_the_ts_golden() {
    let script = json!({ "responses": ["unused"] });
    let mut client = AcpChild::spawn(&["--mode", "acp", "--no-session"], &script);
    let id = client.request("initialize", &initialize_params());
    let (response, notifications) = client.wait_response(id, TIMEOUT);
    assert!(notifications.is_empty(), "nothing precedes initialize");
    let result = &response["result"];
    assert_eq!(result["protocolVersion"], 1);
    let capabilities = &result["agentCapabilities"];
    assert_eq!(capabilities["loadSession"], false);
    assert_eq!(
        capabilities["promptCapabilities"],
        json!({ "image": true, "embeddedContext": true })
    );
    assert_eq!(capabilities["sessionCapabilities"], json!({ "close": {} }));
    // ACP MCP server admission is served, so the TS `mcpCapabilities`
    // flag (http support) is advertised.
    assert_eq!(capabilities["mcpCapabilities"], json!({ "http": true }));
    let info = &result["agentInfo"];
    assert_eq!(info["name"], "eukhe");
    assert_eq!(info["title"], "Eukhe");
    assert_eq!(result["_meta"], json!({ "com.eukhe": {} }));
}

#[test]
fn acp_second_initialize_is_served() {
    let script = json!({ "responses": ["unused"] });
    let mut client = AcpChild::spawn(&["--mode", "acp"], &script);
    let first = client.request("initialize", &initialize_params());
    let _ = client.wait_response(first, TIMEOUT);
    let second = client.request("initialize", &initialize_params());
    let (response, _) = client.wait_response(second, TIMEOUT);
    assert_eq!(response["result"]["protocolVersion"], 1);
}

#[test]
fn acp_prompt_stream_completion_envelope_and_stop_reason_match_ts() {
    let script = json!({ "engine": "faux", "responses": ["ACP-OK"] });
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
        &json!({ "sessionId": session_id, "prompt": [{ "type": "text", "text": "Reply with exactly: ACP-OK" }] }),
    );
    let (prompt_response, updates) = client.wait_response(prompt, TIMEOUT);

    // Frame shape sequence from ts-happy_path.jsonl: the chunk stream, the
    // response boundary, the completion event, the terminal envelope, and
    // then the response. The faux provider emits its text in one chunk.
    let mut shapes = Vec::new();
    for update in &updates {
        let body = &update["params"]["update"];
        let meta = &body["_meta"]["com.eukhe"];
        shapes.push((
            body["sessionUpdate"]
                .as_str()
                .unwrap_or_default()
                .to_string(),
            meta["phase"].as_str().unwrap_or_default().to_string(),
            meta["outcome"].as_str().map(str::to_string),
            meta["terminalQuiescenceExpected"].as_bool(),
        ));
    }
    let boundary = (
        "session_info_update".to_string(),
        "responseBoundary".to_string(),
        Some("result".to_string()),
        Some(true),
    );
    let completion = (
        "session_info_update".to_string(),
        "event".to_string(),
        None,
        None,
    );
    let terminal = (
        "session_info_update".to_string(),
        "terminalQuiescence".to_string(),
        Some("result".to_string()),
        None,
    );
    assert_eq!(
        shapes.first().map(|(tag, _, _, _)| tag.clone()),
        Some("agent_message_chunk".to_string())
    );
    assert!(shapes.contains(&boundary), "shapes: {shapes:?}");
    assert!(shapes.contains(&completion), "shapes: {shapes:?}");
    assert!(shapes.contains(&terminal), "shapes: {shapes:?}");
    assert_eq!(shapes.last(), Some(&terminal));

    assert_eq!(
        prompt_response["result"],
        json!({ "stopReason": "end_turn" })
    );

    // Sequences are strictly increasing across the whole turn.
    let mut sequences: Vec<u64> = Vec::new();
    for update in &updates {
        sequences.push(
            update["params"]["update"]["_meta"]["com.eukhe"]["eventSequence"]
                .as_u64()
                .unwrap(),
        );
    }
    let mut sorted = sequences.clone();
    sorted.sort_unstable();
    sorted.dedup();
    assert_eq!(sequences, sorted, "eventSequence strictly increases");

    let close = client.request("session/close", &json!({ "sessionId": session_id }));
    let (close_response, _) = client.wait_response(close, TIMEOUT);
    assert_eq!(close_response["result"], json!({}));
}

#[test]
fn acp_prompt_chunk_carries_the_assistant_message_id() {
    let script = json!({ "engine": "faux", "responses": ["ACP-OK"] });
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
        &json!({ "sessionId": session_id, "prompt": [{ "type": "text", "text": "hello" }] }),
    );
    let (_, updates) = client.wait_response(prompt, TIMEOUT);
    let chunk = updates
        .iter()
        .find(|update| update["params"]["update"]["sessionUpdate"] == "agent_message_chunk")
        .expect("a message chunk");
    assert_eq!(chunk["params"]["update"]["messageId"], "eukhe-assistant-1");
    assert_eq!(
        chunk["params"]["update"]["content"],
        json!({ "type": "text", "text": "ACP-OK" })
    );
    assert_eq!(
        chunk["params"]["update"]["_meta"]["com.eukhe"],
        json!({ "promptTurnId": 1, "eventSequence": 1, "phase": "event" })
    );
}

#[test]
fn acp_cwd_mismatch_is_reported_not_adopted() {
    let script = json!({ "responses": ["unused"] });
    let mut client = AcpChild::spawn(&["--mode", "acp", "--no-session"], &script);
    let init = client.request("initialize", &initialize_params());
    let _ = client.wait_response(init, TIMEOUT);
    let new = client.request("session/new", &json!({ "cwd": "/tmp", "mcpServers": [] }));
    let (new_response, _) = client.wait_response(new, TIMEOUT);
    let meta = &new_response["result"]["_meta"]["com.eukhe"]["cwd"];
    assert_eq!(meta["requested"], "/tmp");
    // The actual cwd is the temp dir the client runs in; only the mismatch
    // shape is asserted here (the value is tempdir-random).
    assert!(meta["actual"]
        .as_str()
        .is_some_and(|actual| actual.starts_with(std::path::MAIN_SEPARATOR)));
}

#[test]
fn acp_error_shapes_match_the_ts_goldens() {
    let script = json!({ "responses": ["unused"] });
    let mut client = AcpChild::spawn(&["--mode", "acp", "--no-session"], &script);
    let init = client.request("initialize", &initialize_params());
    let _ = client.wait_response(init, TIMEOUT);

    // Unknown session (ts-errors.jsonl): -32603 with the details string.
    let prompt = client.request(
        "session/prompt",
        &json!({ "sessionId": "bogus-session", "prompt": [{ "type": "text", "text": "hi" }] }),
    );
    let (response, _) = client.wait_response(prompt, TIMEOUT);
    assert_eq!(response["error"]["code"], -32603);
    assert_eq!(response["error"]["message"], "Internal error");
    assert_eq!(
        response["error"]["data"]["details"],
        "Unknown ACP session: bogus-session"
    );

    let close = client.request("session/close", &json!({ "sessionId": "bogus-session" }));
    let (response, _) = client.wait_response(close, TIMEOUT);
    assert_eq!(
        response["error"]["data"]["details"],
        "Unknown ACP session: bogus-session"
    );

    let new = client.request("session/new", &json!({ "mcpServers": [] }));
    let (new_response, _) = client.wait_response(new, TIMEOUT);
    let session_id = new_response["result"]["sessionId"]
        .as_str()
        .unwrap()
        .to_string();

    // Second session/new on a live connection (ts-errors.jsonl).
    let again = client.request("session/new", &json!({ "mcpServers": [] }));
    let (response, _) = client.wait_response(again, TIMEOUT);
    assert_eq!(response["error"]["code"], -32603);
    assert_eq!(
        response["error"]["data"]["details"],
        "eukhe ACP mode hosts one session per connection; start another eukhe process for a second session"
    );

    // Unknown method (ts-errors.jsonl): -32601 with the observed message.
    let unknown = client.request("unknown/method", &json!({}));
    let (response, _) = client.wait_response(unknown, TIMEOUT);
    assert_eq!(response["error"]["code"], -32601);
    assert_eq!(
        response["error"]["message"],
        "\"Method not found\": unknown/method"
    );
    assert_eq!(response["error"]["data"]["method"], "unknown/method");

    let close = client.request("session/close", &json!({ "sessionId": session_id }));
    let (response, _) = client.wait_response(close, TIMEOUT);
    assert_eq!(response["result"], json!({}));
}

#[test]
fn acp_initialize_with_string_protocol_version_is_invalid_params() {
    let script = json!({ "responses": ["unused"] });
    let mut client = AcpChild::spawn(&["--mode", "acp", "--no-session"], &script);
    let id = client.request(
        "initialize",
        &json!({ "protocolVersion": "1", "clientCapabilities": {} }),
    );
    let (response, _) = client.wait_response(id, TIMEOUT);
    assert_eq!(response["error"]["code"], -32602);
    assert_eq!(response["error"]["message"], "Invalid params");
    assert_eq!(
        response["error"]["data"]["protocolVersion"]["_errors"][0],
        "Invalid input: expected number, received string"
    );
}

#[test]
fn acp_image_block_without_mime_type_is_invalid_params() {
    let script = json!({ "responses": ["unused"] });
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
        &json!({ "sessionId": session_id, "prompt": [{ "type": "image", "data": "AAAA" }] }),
    );
    let (response, _) = client.wait_response(prompt, TIMEOUT);
    assert_eq!(response["error"]["code"], -32602);
    assert_eq!(response["error"]["message"], "Invalid params");
    assert_eq!(
        response["error"]["data"]["reason"],
        "image block requires base64 `data` and `mimeType` strings"
    );
}

#[test]
fn acp_cancel_without_an_active_turn_is_a_noop() {
    let script = json!({ "responses": ["unused"] });
    let mut client = AcpChild::spawn(&["--mode", "acp", "--no-session"], &script);
    let init = client.request("initialize", &initialize_params());
    let _ = client.wait_response(init, TIMEOUT);
    let new = client.request("session/new", &json!({ "mcpServers": [] }));
    let (new_response, _) = client.wait_response(new, TIMEOUT);
    let session_id = new_response["result"]["sessionId"]
        .as_str()
        .unwrap()
        .to_string();

    client.notify("session/cancel", &json!({ "sessionId": session_id }));
    // The no-op cancel answers nothing; the session still closes cleanly.
    let close = client.request("session/close", &json!({ "sessionId": session_id }));
    let (close_response, notifications) = client.wait_response(close, TIMEOUT);
    assert!(notifications.is_empty(), "a no-op cancel publishes nothing");
    assert_eq!(close_response["result"], json!({}));
}

#[test]
fn acp_mcp_admission_accepts_valid_servers_and_close_releases() {
    let script = json!({ "responses": ["unused"] });
    let mut client = AcpChild::spawn(&["--mode", "acp", "--no-session"], &script);
    let init = client.request("initialize", &initialize_params());
    let _ = client.wait_response(init, TIMEOUT);
    let new = client.request(
        "session/new",
        &json!({ "mcpServers": [
            { "name": "capture-stdio", "type": "stdio", "command": "cat", "args": [], "env": [{"name": "A", "value": "1"}] },
            { "name": "capture-http", "type": "http", "url": "https://mcp.invalid/capture", "headers": [{"name": "X-A", "value": "yes"}] },
        ]}),
    );
    let (response, _) = client.wait_response(new, TIMEOUT);
    let session_id = response["result"]["sessionId"]
        .as_str()
        .expect("admission succeeds")
        .to_string();
    let close = client.request("session/close", &json!({ "sessionId": session_id }));
    let (close_response, _) = client.wait_response(close, TIMEOUT);
    assert_eq!(close_response["result"], json!({}));
}

#[test]
fn acp_mcp_admission_rejects_a_second_session_only_when_open() {
    let script = json!({ "responses": ["unused"] });
    let mut client = AcpChild::spawn(&["--mode", "acp", "--no-session"], &script);
    let init = client.request("initialize", &initialize_params());
    let _ = client.wait_response(init, TIMEOUT);
    let new = client.request(
        "session/new",
        &json!({ "mcpServers": [
            { "name": "first", "type": "stdio", "command": "cat", "args": [], "env": [] },
        ]}),
    );
    let (response, _) = client.wait_response(new, TIMEOUT);
    let session_id = response["result"]["sessionId"]
        .as_str()
        .expect("admission succeeds")
        .to_string();
    // Rejected admission keeps serving: the single-session error is
    // internal with the raw details, exactly like the TS host.
    let second = client.request(
        "session/new",
        &json!({ "mcpServers": [
            { "name": "second", "type": "stdio", "command": "cat", "args": [], "env": [] },
        ]}),
    );
    let (second_response, _) = client.wait_response(second, TIMEOUT);
    assert_eq!(second_response["error"]["code"], -32603);
    assert_eq!(second_response["error"]["message"], "Internal error");
    assert_eq!(
        second_response["error"]["data"]["details"],
        "eukhe ACP mode hosts one session per connection; start another eukhe process for a second session"
    );
    // Close, then a replacement admission with a different server list.
    let close = client.request("session/close", &json!({ "sessionId": session_id }));
    let (close_response, _) = client.wait_response(close, TIMEOUT);
    assert_eq!(close_response["result"], json!({}));
    let replacement = client.request(
        "session/new",
        &json!({ "mcpServers": [
            { "name": "replacement", "type": "stdio", "command": "cat", "args": [], "env": [] },
        ]}),
    );
    let (replacement_response, _) = client.wait_response(replacement, TIMEOUT);
    assert!(
        replacement_response["result"]["sessionId"].is_string(),
        "replacement admission succeeds"
    );
}

#[test]
fn acp_mcp_admission_rejects_invalid_params_with_the_ts_reasons() {
    let script = json!({ "responses": ["unused"] });
    let cases: &[(Value, &str)] = &[
        (
            json!([{ "name": "-bad", "type": "stdio", "command": "cat", "args": [], "env": [] }]),
            "MCP server names must start with an alphanumeric character and contain at most 64 alphanumeric, underscore, or hyphen characters",
        ),
        (
            json!([
                { "name": "dup", "type": "stdio", "command": "cat", "args": [], "env": [] },
                { "name": "dup", "type": "stdio", "command": "cat", "args": [], "env": [] },
            ]),
            "duplicate MCP server name: dup",
        ),
        (
            json!([{ "name": "n", "type": "stdio", "command": "cat\u{0}", "args": [], "env": [] }]),
            "MCP server n has an invalid stdio command",
        ),
        (
            json!([{ "name": "e", "type": "stdio", "command": "cat", "args": [], "env": [
                { "name": "A", "value": "1" }, { "name": "A", "value": "2" },
            ]}]),
            "MCP server e has duplicate environment A",
        ),
        (
            json!([{ "name": "h", "type": "http", "url": "https://mcp.invalid/x", "headers": [
                { "name": "X-A", "value": "1" }, { "name": "x-a", "value": "2" },
            ]}]),
            "MCP server h has duplicate header x-a",
        ),
        (
            json!([{ "name": "s", "type": "sse", "url": "https://mcp.invalid/x", "headers": [] }]),
            "MCP server s uses unsupported sse transport",
        ),
        (
            json!([{ "name": "c", "type": "http", "url": "https://user:pw@mcp.invalid/x", "headers": [] }]),
            "MCP server c must use an HTTP(S) URL without embedded credentials",
        ),
    ];
    for (servers, reason) in cases {
        let mut client = AcpChild::spawn(&["--mode", "acp", "--no-session"], &script);
        let init = client.request("initialize", &initialize_params());
        let _ = client.wait_response(init, TIMEOUT);
        let new = client.request("session/new", &json!({ "mcpServers": servers }));
        let (response, _) = client.wait_response(new, TIMEOUT);
        assert_eq!(response["error"]["code"], -32602, "case {reason}");
        assert_eq!(response["error"]["message"], "Invalid params");
        assert_eq!(response["error"]["data"]["reason"], *reason);
    }
}

#[test]
fn acp_mcp_schema_invalid_entries_are_dropped_like_the_sdk() {
    // The SDK zod filter (`vecSkipError(zMcpServer)`) silently drops
    // entries that miss required fields; admission succeeds with the
    // surviving list — the live TS behavior.
    let script = json!({ "responses": ["unused"] });
    let mut client = AcpChild::spawn(&["--mode", "acp", "--no-session"], &script);
    let init = client.request("initialize", &initialize_params());
    let _ = client.wait_response(init, TIMEOUT);
    let new = client.request(
        "session/new",
        // No `env` (required), invalid env item, http without headers.
        &json!({ "mcpServers": [
            { "name": "no-env", "type": "stdio", "command": "cat", "args": [] },
            { "name": "bad-item", "type": "stdio", "command": "cat", "args": [], "env": [{"name": 1, "value": "x"}] },
            { "name": "no-headers", "type": "http", "url": "https://mcp.invalid/x" },
        ]}),
    );
    let (response, _) = client.wait_response(new, TIMEOUT);
    assert!(
        response["result"]["sessionId"].is_string(),
        "schema-invalid entries are dropped, not rejected"
    );
}

#[test]
fn acp_mcp_long_names_fail_at_tool_derivation_with_internal_error() {
    let script = json!({ "responses": ["unused"] });
    let mut client = AcpChild::spawn(&["--mode", "acp", "--no-session"], &script);
    let init = client.request("initialize", &initialize_params());
    let _ = client.wait_response(init, TIMEOUT);
    let long = format!("a{}", "b".repeat(50));
    let new = client.request(
        "session/new",
        &json!({ "mcpServers": [
            { "name": long, "type": "stdio", "command": "cat", "args": [], "env": [] },
        ]}),
    );
    let (response, _) = client.wait_response(new, TIMEOUT);
    assert_eq!(response["error"]["code"], -32603);
    assert_eq!(
        response["error"]["data"]["details"],
        format!("Invalid ACP MCP server name: {long}")
    );
}

#[test]
fn acp_daemon_attached_cancels_mid_turn() {
    // A scripted worker with a slow turn: the cancel lands while the
    // turn runs, and the prompt resolves `{stopReason: "cancelled"}`
    // with no boundary frames — the TS daemon-attached cancel shape.
    let mut client = AcpChild::spawn(
        &["--mode", "acp", "--no-session"],
        &json!({ "responses": [{ "text": "a slow answer", "delayMs": 8000 }] }),
    );
    let init = client.request("initialize", &initialize_params());
    let _ = client.wait_response(init, TIMEOUT);
    let new = client.request("session/new", &json!({ "mcpServers": [] }));
    let (new_response, _) = client.wait_response(new, Duration::from_mins(1));
    let session_id = new_response["result"]["sessionId"]
        .as_str()
        .unwrap()
        .to_string();
    let prompt = client.request(
            "session/prompt",
            &json!({ "sessionId": session_id, "prompt": [{ "type": "text", "text": "a slow question" }] }),
        );
    // The turn is mid-delay: cancel, then wait for the prompt response.
    client.notify("session/cancel", &json!({ "sessionId": session_id }));
    let (prompt_response, updates) = client.wait_response(prompt, Duration::from_mins(1));
    assert_eq!(prompt_response["result"]["stopReason"], "cancelled");
    assert!(
        updates.is_empty(),
        "a cancelled turn publishes no boundary frames after the cancel"
    );
    let close = client.request("session/close", &json!({ "sessionId": session_id }));
    let (close_response, _) = client.wait_response(close, Duration::from_mins(1));
    assert_eq!(close_response["result"], json!({}));
    drop(client);
}

#[test]
fn acp_daemon_attached_overlapping_prompt_is_refused() {
    // A second prompt while the first runs is refused; the running turn
    // is untouched and the next prompt after its settle runs.
    let mut client = AcpChild::spawn(
        &["--mode", "acp", "--no-session"],
        &json!({ "engine": "faux", "tokensPerSecond": 2, "responses": [
            { "text": "a paced answer that streams slowly enough to overlap a prompt" },
            "SECOND-OK",
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
    // Readiness is the turn's own first streamed chunk, not a timer.
    client.wait_update("agent_message_chunk", TIMEOUT);
    let second = client.request(
        "session/prompt",
        &json!({ "sessionId": session_id, "prompt": [{ "type": "text", "text": "the overlap" }] }),
    );
    let (second_response, _) = client.wait_response(second, TIMEOUT);
    assert_eq!(
        second_response["error"]["code"], -32603,
        "the overlapping prompt is refused: {second_response}"
    );
    assert!(
        second_response["error"]["data"]["details"]
            .as_str()
            .unwrap_or_default()
            .contains("A prompt turn is already running for this ACP session"),
        "the refusal names the running-turn rule: {second_response}"
    );
    let (first_response, _) = client.wait_response(first, TIMEOUT);
    assert_eq!(
        first_response["result"]["stopReason"], "end_turn",
        "the refused overlap never touched the running turn: {first_response}"
    );
    let third = client.request(
        "session/prompt",
        &json!({ "sessionId": session_id, "prompt": [{ "type": "text", "text": "after the settle" }] }),
    );
    let (third_response, updates) = client.wait_response(third, TIMEOUT);
    assert_eq!(
        third_response["result"]["stopReason"], "end_turn",
        "the turn slot frees at the settle: {third_response}"
    );
    let chunk = updates
        .iter()
        .find(|update| update["params"]["update"]["sessionUpdate"] == "agent_message_chunk")
        .expect("the next turn streams its scripted answer");
    assert_eq!(
        chunk["params"]["update"]["content"],
        json!({ "type": "text", "text": "SECOND-OK" })
    );
}

#[test]
fn acp_daemon_attached_close_mid_turn_answers_cancelled() {
    let mut client = AcpChild::spawn(
        &["--mode", "acp", "--no-session"],
        &json!({ "engine": "faux", "tokensPerSecond": 2, "responses": [
            { "text": "a paced answer that streams slowly enough to close mid-turn" },
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
    let prompt = client.request(
        "session/prompt",
        &json!({ "sessionId": session_id, "prompt": [{ "type": "text", "text": "a slow question" }] }),
    );
    client.wait_update("agent_message_chunk", TIMEOUT);
    let close = client.request("session/close", &json!({ "sessionId": session_id }));
    let (prompt_response, frames) = client.wait_response(prompt, TIMEOUT);
    assert_eq!(
        prompt_response["result"]["stopReason"], "cancelled",
        "a prompt closed mid-turn answers cancelled: {prompt_response}"
    );
    let close_response = frames
        .into_iter()
        .find(|frame| frame["id"] == close)
        .unwrap_or_else(|| client.wait_response(close, TIMEOUT).0);
    assert_eq!(close_response["result"], json!({}));
}
