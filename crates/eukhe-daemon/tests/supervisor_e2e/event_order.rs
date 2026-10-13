//! The per-client writer keeps the worker's event-before-response order:
//! a slow reader's reply never jumps the session events queued ahead of it.

use super::*;

/// A wire offset no kernel socket buffer reaches: a blocked writer has
/// handed the kernel at most its socket buffers plus one partial line
/// (the defaults are far smaller - Linux ~208 KiB, macOS 8 KiB), so an
/// event starting past this offset was queued in the supervisor behind
/// the blocked write.
const SOCKET_SLACK: usize = 1 << 20;

/// A slow reader's `prompt_and_wait` reply trails every session event the
/// turn emitted before it, even while the writer is backlogged: the worker
/// writes a turn's frames before the reply on its own socket, and the
/// per-client writer polls its session-event arm ahead of the response
/// arm, so the reply cannot jump the events queued ahead of it.
///
/// The backlog is built by size, not by time: the prompt is longer than
/// [`SOCKET_SLACK`] and the turn echoes it whole in the user message's
/// `message_start`, so a client that reads nothing blocks the writer
/// inside that frame, and every later frame of the turn starts past the
/// slack. The script fixes those frames whatever the streaming pace (the
/// harness may fold a fast stream's updates into its `message_end`): the
/// user `message_end`; a tool turn whose unknown tool answers at once
/// with an error result (the call's message pair, `tool_execution_end`,
/// the result's message pair, `turn_end`); and the closing turn
/// (`turn_start`, the answer's message pair, `turn_end`, `agent_end`).
/// Those twelve exceed the asserted minimum of eight, so only a turn that
/// builds no queue fails it.
/// A second connection's `wait_for_idle` answer is the readiness signal.
/// The precondition: a blocked writer can have handed the kernel only its
/// socket buffers plus one partial line, so a pre-reply session event at
/// a wire offset past [`SOCKET_SLACK`] was still queued in the supervisor
/// when `wait_for_idle` answered.
#[test]
fn slow_client_reads_turn_events_before_the_reply() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let socket = dir.path().join("daemon.sock");
    let agent_dir = dir.path().join("agent");
    std::fs::create_dir_all(&agent_dir).expect("agent dir");
    // Unpaced, short answers: the turn costs the prompt's linear handling,
    // a fraction of the response budget.
    let script_path = dir.path().join("script.json");
    std::fs::write(
        &script_path,
        serde_json::json!({
            "engine": "faux",
            "responses": [
                { "content": [
                    { "type": "toolCall", "name": "no-such-tool", "arguments": {} },
                ] },
                { "text": "done" },
            ],
        })
        .to_string(),
    )
    .expect("write script");
    let _daemon = spawn_daemon(&socket, &agent_dir);
    let (mut slow, _hello) = Client::connect(&socket);
    slow.send_command(
        "c1",
        &serde_json::json!({
            "type": "create",
            "config": {
                "cwd": dir.path().to_string_lossy(),
                "sessionDir": agent_dir.join("sessions").to_string_lossy(),
                "script": script_path.to_string_lossy(),
            },
        }),
    );
    let created = slow.read_response("c1");
    assert_eq!(created["success"], true, "create failed: {created}");
    let session_id = created["data"]["id"]
        .as_str()
        .or_else(|| created["data"]["sessionId"].as_str())
        .expect("session id in create response")
        .to_string();
    slow.send_command(
        "a1",
        &serde_json::json!({ "type": "attach", "activeSessionId": session_id }),
    );
    assert_eq!(slow.read_response("a1")["success"], true, "attach failed");
    // The probe subscribes before the turn starts, and asks for idle only
    // after reading the turn's `agent_start`: `wait_for_idle` on an idle
    // session answers at once, and the observed `agent_start` is what
    // orders the probe's dispatch behind the slow client's prompt.
    let (mut probe, _hello) = Client::connect(&socket);
    probe.send_command(
        "a2",
        &serde_json::json!({ "type": "attach", "activeSessionId": session_id }),
    );
    let (probe_attach, mut probe_lines) = probe.read_response_and_lines("a2");
    assert_eq!(
        probe_attach["success"], true,
        "probe attach failed: {probe_attach}"
    );
    // The turn runs while this client reads nothing: the writer blocks
    // inside the prompt's echo, with the turn's remaining events queued
    // behind the blocked write.
    slow.send_command(
        "p1",
        &serde_json::json!({
            "type": "prompt_and_wait",
            "activeSessionId": session_id,
            "message": "y".repeat(SOCKET_SLACK),
        }),
    );
    let _ = probe.take_session_event(&mut probe_lines, "agent_start");
    // Readiness is observed, never timed: the probe's `wait_for_idle`
    // answers once the worker settled the turn, so every frame of the
    // turn is published and the reply is on its way through dispatch.
    probe.send_command(
        "w1",
        &serde_json::json!({ "type": "wait_for_idle", "activeSessionId": session_id }),
    );
    let idle = probe.read_response("w1");
    assert_eq!(idle["success"], true, "wait_for_idle failed: {idle}");
    // Drain the backlog: the writer owes this client every queued event
    // before the reply. The offset counts the wire bytes read since the
    // backlog began: the kernel can be holding only a socket buffer's
    // worth plus one partial line, so every counted event was still
    // queued in the supervisor behind the blocked write when
    // `wait_for_idle` answered; the turn's boundary frames must be among
    // the pre-reply events.
    let mut wire_offset = 0usize;
    let mut queued_before_reply = 0usize;
    let mut saw_turn_end = false;
    let mut saw_agent_end = false;
    let reply = loop {
        let line = slow.read_line();
        if line.get("id").and_then(|value| value.as_str()) == Some("p1") {
            break line;
        }
        if line["type"] == "session_event" {
            if wire_offset >= SOCKET_SLACK {
                queued_before_reply += 1;
            }
            match line["event"]["type"].as_str() {
                Some("turn_end") => saw_turn_end = true,
                Some("agent_end") => saw_agent_end = true,
                _ => {}
            }
        }
        wire_offset += serde_json::to_string(&line)
            .expect("re-serialize line")
            .len();
    };
    assert_eq!(reply["success"], true, "prompt_and_wait failed: {reply}");
    assert!(
        queued_before_reply >= 8,
        "the reply must trail >= 8 session events past the slack, got {queued_before_reply}"
    );
    assert!(saw_turn_end, "the turn's turn_end must precede the reply");
    assert!(saw_agent_end, "the turn's agent_end must precede the reply");
}
