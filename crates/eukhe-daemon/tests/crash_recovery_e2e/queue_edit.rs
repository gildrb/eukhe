//! Exactly-once queue edits (spec O1, O5, O7): a queue edit withdraws the
//! queued inputs from the edited position on and admits them again in the
//! new order. A real worker is killed (`SIGKILL`) at each point of the edit
//! (`EUKHE_TEST_KILL_AT=message:<point>`: `intended` once the inputs to
//! admit again are stashed durably, `started` once they are withdrawn,
//! `finished` once the store is final); after the restart and a
//! `resume_queue`, every queued input is delivered exactly once: none lost
//! to the withdrawal, none doubled by the stash or a repeated admission.

use super::*;

/// The stored user entries whose text is `message`.
fn user_entries(world: &World, message: &str) -> usize {
    world
        .transcript()
        .of_kind("pi.user")
        .iter()
        .filter(|entry| entry["model"][0]["content"][0]["text"] == message)
        .count()
}

fn queue_edit_killed_at(point: &str) {
    let marks = tempfile::tempdir().expect("marker dir");
    let marker = marks.path().join("killed");
    let world = World::with_env(
        128_000,
        &json!({}),
        &[(
            "EUKHE_TEST_KILL_AT",
            format!("message:{point}@{}", marker.display()),
        )],
    );
    let mut client = world.connect();
    let session_id = world.create(&mut client, 1);
    let busy = prompt("busy", &[HOLD_STREAM], 0);
    client.send(&json!({ "type": "prompt", "activeSessionId": session_id, "message": busy }));
    world.mock.wait_for(WAIT, "the held answer stream", |log| {
        log.iter()
            .any(|entry| entry.holding && entry.request.prompt.contains(HOLD_STREAM))
            .then_some(())
    });
    let queued: Vec<String> = ["q1", "q2", "q3"]
        .iter()
        .map(|tag| prompt(tag, &[], 0))
        .collect();
    for message in &queued {
        let followed = client.request(
            &json!({ "type": "follow_up", "activeSessionId": session_id, "message": message }),
            WAIT,
        );
        assert_eq!(followed["success"], true, "follow_up: {followed}");
    }
    let pid = worker_pid(&mut client, &session_id);
    // Move the first queued input back one place: q1 and q2 are withdrawn
    // and admitted again as q2, q1.
    client.send(&json!({
        "type": "mutate_queued_message",
        "activeSessionId": session_id,
        "lane": "followUp",
        "index": 0,
        "expectedText": queued[0],
        "mutation": { "type": "move", "direction": 1 },
    }));
    let deadline = Instant::now() + WAIT;
    while !marker.exists() {
        assert!(
            Instant::now() < deadline,
            "message:{point} was never reached\n{}",
            world.diagnostics()
        );
        std::thread::sleep(Duration::from_millis(20));
    }
    wait_dead(pid);
    drop(client);
    let mut client = reattach(&world, &session_id);
    // Inputs a crash left stashed come back with the queue's resume; one
    // already admitted again dedupes on its request id.
    let _ = client.request(
        &json!({ "type": "resume_queue", "activeSessionId": session_id }),
        WAIT,
    );
    world.mock.open_gate(STREAM_GATE);
    wait_idle(&mut client, &session_id);
    let _ = client.request(
        &json!({ "type": "resume_queue", "activeSessionId": session_id }),
        WAIT,
    );
    wait_idle(&mut client, &session_id);
    for message in &queued {
        assert_eq!(
            user_entries(&world, message),
            1,
            "{message} is delivered once\n{}",
            world.diagnostics()
        );
    }
    assert_eq!(user_entries(&world, &busy), 1);
}

#[test]
fn a_queue_edit_killed_after_its_stash_delivers_each_input_once() {
    queue_edit_killed_at("intended");
}

#[test]
fn a_queue_edit_killed_after_its_withdrawals_delivers_each_input_once() {
    queue_edit_killed_at("started");
}

#[test]
fn a_queue_edit_killed_after_it_finished_delivers_each_input_once() {
    queue_edit_killed_at("finished");
}
