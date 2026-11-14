//! Exactly-once model requests (spec O1, O4, O7): a request is intended
//! when its checkpoint commits, started when one more send commits before
//! it goes out, finished when its reply commits. A real worker is killed
//! (`SIGKILL`) at each point and mid-stream; after the restart:
//!
//! - a request killed before it went out goes out once,
//! - a request whose reply committed never goes out again,
//! - a request cut mid-stream to a provider that declares no
//!   deduplication is never sent again: it is listed unknown by
//!   `get_unknown_effects` and the run goes on with a new request (a new
//!   `Idempotency-Key`), at most `retry.maxRetries` times in a row; past
//!   that the run ends with an error saying so,
//! - a request cut mid-stream to a provider whose models.json declares
//!   `"requestDedup": "lasting"` goes out again under the same key, at most
//!   `retry.maxResends` times; past that it is listed unknown and the run
//!   goes on with a new request.

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
/// cannot tell whether it went out, so it is listed unknown and never
/// sent again; the run goes on with a new request, answered once.
#[test]
fn a_request_killed_after_its_start_is_replaced_by_a_new_one() {
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

/// In `world`, hold the `crash` turn's answer mid-stream and kill the
/// worker `kills` times (each relaunch sends a request again, the same or
/// a new one, and holds it once more); answers the session, a client and
/// the prompt. `limits`: a budget the session is given before the prompt.
fn killed_mid_stream(
    world: &World,
    kills: usize,
    limits: Option<Value>,
) -> (String, WireClient, String) {
    let mut client = world.connect();
    let session_id = world.create(&mut client, 1);
    if let Some(limits) = limits {
        let set = client.request(
            &json!({ "type": "set_budget", "activeSessionId": session_id, "limits": limits }),
            WAIT,
        );
        assert_eq!(set["success"], true, "set_budget: {set}");
    }
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
        client = reattach(world, &session_id);
    }
    (session_id, client, message)
}

/// The keys the sends of the `crash` turn carried, in order.
fn keys(sent: &[Logged]) -> Vec<Option<String>> {
    sent.iter()
        .map(|entry| entry.request.idempotency_key.clone())
        .collect()
}

/// The money the session's budget held for the request sent under `key`
/// when the restart found it in flight: what the recovery charged it at.
fn held_at_recovery(world: &World, key: &str) -> u64 {
    let budgets = world.agent_dir.join("budgets");
    let ledgers: Vec<PathBuf> = std::fs::read_dir(&budgets)
        .expect("the budgets dir")
        .flatten()
        .map(|entry| entry.path())
        .filter(|path| {
            path.extension()
                .is_some_and(|extension| extension == "jsonl")
        })
        .collect();
    assert_eq!(ledgers.len(), 1, "one account: {ledgers:?}");
    let records: Vec<Value> = std::fs::read_to_string(&ledgers[0])
        .expect("the ledger")
        .lines()
        .map(|line| serde_json::from_str(line).expect("a ledger line"))
        .collect();
    let before = records
        .windows(2)
        .find(|pair| pair[1]["op"]["kind"] == "recover")
        .map(|pair| pair[0].clone())
        .expect("a recovery");
    before["state"]["account"]["holds"]
        .as_array()
        .expect("holds")
        .iter()
        .filter(|hold| hold["key"] == key)
        .map(|hold| hold["amount"]["costMicros"].as_u64().unwrap_or(0))
        .sum()
}

/// Cut mid-stream once, the provider declaring no deduplication, in a
/// session whose budget limits money: the restart never sends it again;
/// the run goes on with a new request under a new key, which is answered,
/// and the cut request is listed unknown with what was cut, why, and the
/// money its reservation still holds counted (what the recovery charged).
#[test]
fn an_undeclared_request_cut_mid_stream_is_replaced_by_a_new_one() {
    let world = World::priced(128_000, &json!({}));
    let (session_id, mut client, message) =
        killed_mid_stream(&world, 1, Some(json!({ "costMicros": 5_000_000 })));
    world.mock.open_gate(STREAM_GATE);
    wait_idle(&mut client, &session_id);
    assert_transcript(&world, &[message]);
    let sent = turn_requests(&world, "crash");
    assert_eq!(sent.len(), 2, "{:?}", mock_llm::summary(&world.mock.log()));
    let keys = keys(&sent);
    assert!(
        keys.iter().all(Option::is_some),
        "every send is keyed: {keys:?}"
    );
    assert_ne!(keys[0], keys[1], "the new request has a new key");
    assert_eq!(answers(&world, "crash"), 1);
    let held = held_at_recovery(&world, keys[0].as_deref().expect("a key"));
    assert!(held > 0, "the cut request held money");
    let effects = unknown_effects(&mut client, &session_id);
    assert_eq!(effects.len(), 1, "one interrupted request: {effects:?}");
    assert_eq!(effects[0]["kind"], "request");
    assert!(effects[0].get("resolution").is_none(), "{effects:?}");
    assert_eq!(
        effects[0]["what"],
        format!(
            "Model request to mock/{MODEL} cut by a crash, not resent (no deduplication \
             declared). Up to {} stays counted until its usage is known.",
            eukhe_types::budget::dollars(held)
        )
    );
}

/// Cut mid-stream once, the provider declaring that it drops every repeat
/// of the key: the restart sends it again under the same key, the run
/// answers once, and nothing is listed unknown.
#[test]
fn a_deduplicated_request_cut_mid_stream_goes_out_again_under_its_key() {
    let world = World::deduplicating(128_000, &json!({}));
    let (session_id, mut client, message) = killed_mid_stream(&world, 1, None);
    world.mock.open_gate(STREAM_GATE);
    wait_idle(&mut client, &session_id);
    assert_transcript(&world, &[message]);
    let sent = turn_requests(&world, "crash");
    assert_eq!(sent.len(), 2, "{:?}", mock_llm::summary(&world.mock.log()));
    let keys = keys(&sent);
    assert!(keys[0].is_some(), "the first send carries a key");
    assert_eq!(keys[1], keys[0], "the resend carries the same key");
    assert_eq!(answers(&world, "crash"), 1);
    assert_eq!(
        unknown_effects(&mut client, &session_id),
        Vec::<Value>::new()
    );
}

/// A deduplicated request cut past `retry.maxResends` (0 here): the restart
/// sends it no more; it is listed unknown and the run goes on with a new
/// request, which is answered.
#[test]
fn a_deduplicated_request_cut_past_its_resends_is_replaced_by_a_new_one() {
    let world = World::deduplicating(128_000, &json!({ "retry": { "maxResends": 0 } }));
    let (session_id, mut client, _) = killed_mid_stream(&world, 1, None);
    world.mock.open_gate(STREAM_GATE);
    wait_idle(&mut client, &session_id);
    let sent = turn_requests(&world, "crash");
    assert_eq!(sent.len(), 2, "{:?}", mock_llm::summary(&world.mock.log()));
    let keys = keys(&sent);
    assert_ne!(keys[0], keys[1], "the new request has a new key");
    assert_eq!(answers(&world, "crash"), 1);
    let effects = unknown_effects(&mut client, &session_id);
    assert_eq!(effects.len(), 1, "{effects:?}");
    assert_eq!(
        effects[0]["what"],
        format!("Model request to mock/{MODEL} cut by a crash, not resent (resend limit reached).")
    );
}

/// Cut as many times in a row as `retry.maxRetries` (1 here) allows new
/// requests, and once more: each cut request is listed unknown, none is
/// sent twice, and the run ends with an error that says so; the session
/// still answers the next prompt.
#[test]
fn requests_cut_past_the_retries_end_the_run() {
    let world = World::new(128_000, &json!({ "retry": { "maxRetries": 1 } }));
    let (session_id, mut client, _) = killed_mid_stream(&world, 2, None);
    wait_idle(&mut client, &session_id);
    let sent = turn_requests(&world, "crash");
    assert_eq!(sent.len(), 2, "{:?}", mock_llm::summary(&world.mock.log()));
    let keys: BTreeSet<_> = keys(&sent).into_iter().collect();
    assert_eq!(keys.len(), 2, "every request its own key: {keys:?}");
    assert_eq!(answers(&world, "crash"), 0, "no answer was claimed");
    let effects = unknown_effects(&mut client, &session_id);
    assert_eq!(effects.len(), 2, "two interrupted requests: {effects:?}");
    assert!(effects.iter().all(|effect| effect["kind"] == "request"));
    world.mock.open_gate(STREAM_GATE);
    let next = prompt("next", &[], 0);
    run_turn(&mut client, &session_id, &next);
    assert_eq!(answers(&world, "next"), 1);
}
