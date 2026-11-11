//! Exactly-once model requests (spec O1, O4, O7): a request is intended
//! when its checkpoint commits, started when one more send commits before
//! it goes out, finished when its reply commits. A real worker is killed
//! (`SIGKILL`) at each point and mid-stream; after the restart:
//!
//! - a request killed before it went out goes out once,
//! - a request whose reply committed never goes out again,
//! - a request cut mid-stream goes out again under the same
//!   `Idempotency-Key`, at most `retry.maxResends` times; past that the run
//!   ends with an error saying so, and the request is listed unknown by
//!   `get_unknown_effects`.

use super::*;

/// A world whose processes die at the request's lifecycle point `point`
/// (the first process to pass it; `EUKHE_TEST_KILL_AT`), and the marker
/// file the kill creates.
fn world_killed_at(point: &str, settings: &Value) -> (World, PathBuf, tempfile::TempDir) {
    let marks = tempfile::tempdir().expect("marker dir");
    let marker = marks.path().join("killed");
    let world = World::with_env(
        128_000,
        settings,
        &[(
            "EUKHE_TEST_KILL_AT",
            format!("request:{point}@{}", marker.display()),
        )],
    );
    (world, marker, marks)
}

/// The session's model requests of the turn `tag`.
fn turn_requests(world: &World, tag: &str) -> Vec<Logged> {
    world
        .mock
        .log()
        .into_iter()
        .filter(|entry| {
            entry.request.kind == RequestKind::Turn && prompt_tag(&entry.request.prompt) == tag
        })
        .collect()
}

/// The answers to `tag` the transcript stores.
fn answers(world: &World, tag: &str) -> usize {
    messages_of(&world.transcript(), "assistant")
        .iter()
        .filter(|(_, message)| texts(message).contains(&answer_for(tag)))
        .count()
}

/// The unknown effects the daemon lists for the session.
fn unknown_effects(client: &mut WireClient, session_id: &str) -> Vec<Value> {
    let listed = client.request(
        &json!({ "type": "get_unknown_effects", "activeSessionId": session_id }),
        WAIT,
    );
    assert_eq!(listed["success"], true, "get_unknown_effects: {listed}");
    listed["data"]["effects"]
        .as_array()
        .cloned()
        .unwrap_or_default()
}

/// Prompt `crash` in a world that dies at `point`, wait for the kill, the
/// relaunch and the idle session; answers the world and the session id.
fn crash_at(point: &str) -> (World, String) {
    let (world, marker, _marks) = world_killed_at(point, &json!({}));
    let mut client = world.connect();
    let session_id = world.create(&mut client, 1);
    let pid = worker_pid(&mut client, &session_id);
    let message = prompt("crash", &[], 0);
    client.send(&json!({ "type": "prompt", "activeSessionId": session_id, "message": message }));
    let deadline = Instant::now() + WAIT;
    while !marker.exists() {
        assert!(
            Instant::now() < deadline,
            "request:{point} was never reached\n{}",
            world.diagnostics()
        );
        std::thread::sleep(Duration::from_millis(20));
    }
    wait_dead(pid);
    drop(client);
    let mut client = reattach(&world, &session_id);
    wait_idle(&mut client, &session_id);
    assert_transcript(&world, &[message]);
    (world, session_id)
}

/// Killed once the intent committed and before any send: it goes out once.
#[test]
fn a_request_killed_at_its_intent_goes_out_once() {
    let (world, _) = crash_at("intended");
    let sent = turn_requests(&world, "crash");
    assert_eq!(sent.len(), 1, "{:?}", mock_llm::summary(&world.mock.log()));
    assert_eq!(answers(&world, "crash"), 1);
}

/// Killed once its send committed and before it went out: the restart
/// cannot tell, sends it again under its key (the provider never saw the
/// first), and it is answered once.
#[test]
fn a_request_killed_after_its_start_goes_out_once_more() {
    let (world, _) = crash_at("started");
    let sent = turn_requests(&world, "crash");
    assert_eq!(sent.len(), 1, "{:?}", mock_llm::summary(&world.mock.log()));
    assert!(sent[0].request.idempotency_key.is_some(), "a keyed send");
    assert_eq!(answers(&world, "crash"), 1);
}

/// Killed once its reply committed: never sent again.
#[test]
fn a_request_killed_after_its_reply_committed_never_goes_out_again() {
    let (world, _) = crash_at("finished");
    let sent = turn_requests(&world, "crash");
    assert_eq!(sent.len(), 1, "{:?}", mock_llm::summary(&world.mock.log()));
    assert_eq!(answers(&world, "crash"), 1);
}

/// Hold the `crash` turn's answer mid-stream and kill the worker `kills`
/// times (each relaunch sends the request again and holds it once more);
/// answers the world, the session, a client and the prompt.
fn killed_mid_stream(kills: usize, settings: &Value) -> (World, String, WireClient, String) {
    let world = World::new(128_000, settings);
    let mut client = world.connect();
    let session_id = world.create(&mut client, 1);
    let message = prompt("crash", &[HOLD_STREAM], 0);
    client.send(&json!({ "type": "prompt", "activeSessionId": session_id, "message": message }));
    for kill in 0..kills {
        world.mock.wait_for(WAIT, "the held answer stream", |log| {
            (log.iter()
                .filter(|entry| entry.request.prompt.contains(HOLD_STREAM))
                .count()
                > kill
                && log
                    .iter()
                    .any(|entry| entry.holding && entry.request.prompt.contains(HOLD_STREAM)))
            .then_some(())
        });
        let pid = worker_pid(&mut client, &session_id);
        sigkill(pid);
        wait_dead(pid);
        drop(client);
        client = reattach(&world, &session_id);
    }
    (world, session_id, client, message)
}

/// Cut mid-stream once: the restart sends it again under the same key, and
/// the run answers once.
#[test]
fn a_request_cut_mid_stream_goes_out_again_under_its_key() {
    let (world, session_id, mut client, message) = killed_mid_stream(1, &json!({}));
    world.mock.open_gate(STREAM_GATE);
    wait_idle(&mut client, &session_id);
    assert_transcript(&world, &[message]);
    let sent = turn_requests(&world, "crash");
    assert_eq!(sent.len(), 2, "{:?}", mock_llm::summary(&world.mock.log()));
    let key = sent[0].request.idempotency_key.clone();
    assert!(key.is_some(), "the first send carries a key");
    assert_eq!(
        sent[1].request.idempotency_key, key,
        "the resend carries the same key"
    );
    assert_eq!(answers(&world, "crash"), 1);
    assert_eq!(
        unknown_effects(&mut client, &session_id),
        Vec::<Value>::new()
    );
}

/// Cut mid-stream past `retry.maxResends` (0 here): the restart sends it no
/// more; the run ends with an error that says so, and the request is listed
/// unknown.
#[test]
fn a_request_cut_past_its_resends_ends_the_run_unknown() {
    let (world, session_id, mut client, _) =
        killed_mid_stream(1, &json!({ "retry": { "maxResends": 0 } }));
    wait_idle(&mut client, &session_id);
    let sent = turn_requests(&world, "crash");
    assert_eq!(sent.len(), 1, "{:?}", mock_llm::summary(&world.mock.log()));
    assert_eq!(answers(&world, "crash"), 0, "no answer was claimed");
    let effects = unknown_effects(&mut client, &session_id);
    assert_eq!(effects.len(), 1, "one unknown request: {effects:?}");
    assert_eq!(effects[0]["kind"], "request");
    assert!(effects[0].get("resolution").is_none(), "{effects:?}");
    // The ledger is settled by a client that looked.
    let id = effects[0]["id"].as_str().expect("an effect id");
    let resolved = client.request(
        &json!({
            "type": "resolve_unknown_effect",
            "activeSessionId": session_id,
            "effectId": id,
            "resolution": "notRun",
        }),
        WAIT,
    );
    assert_eq!(resolved["success"], true, "resolve: {resolved}");
    assert_eq!(resolved["data"]["effect"]["resolution"], "notRun");
    // The session still answers the next prompt.
    let next = prompt("next", &[], 0);
    run_turn(&mut client, &session_id, &next);
    assert_eq!(answers(&world, "next"), 1);
}

/// The default cap (2): cut three times, it went out three times under one
/// key, then the run ends unknown.
#[test]
fn a_request_cut_three_times_goes_out_three_times_then_ends_unknown() {
    let (world, session_id, mut client, _) = killed_mid_stream(3, &json!({}));
    wait_idle(&mut client, &session_id);
    let sent = turn_requests(&world, "crash");
    assert_eq!(sent.len(), 3, "{:?}", mock_llm::summary(&world.mock.log()));
    let keys: BTreeSet<_> = sent
        .iter()
        .map(|entry| entry.request.idempotency_key.clone())
        .collect();
    assert_eq!(keys.len(), 1, "one key for every send: {keys:?}");
    assert_eq!(answers(&world, "crash"), 0);
    let effects = unknown_effects(&mut client, &session_id);
    assert_eq!(effects.len(), 1, "{effects:?}");
    assert_eq!(effects[0]["kind"], "request");
}
