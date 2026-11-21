//! Irreversible effects that ran, across a worker crash (spec I2, I4, I6,
//! I8): a `bash` step that talks to a host runs unasked and is recorded
//! once (`e1`, run 1), and the call's result names it. The worker dies
//! while the model answers after the step; the replacement takes the run
//! up again: nothing new is recorded, the ledger holds `e1` as it was,
//! and the run's end reports exactly `e1`, after its `agent_end`. A later
//! run with no irreversible effect reports nothing; the next one reports
//! only its own.

use std::net::TcpListener;

use super::*;

/// The prompt tag the script answers with the `bash` call that talks to
/// the test's host.
pub(crate) const TAG: &str = "[ran-effect]";

/// The gate the answer after an irreversible call waits on, so the test
/// attaches before the run ends.
pub(crate) const REPORT_GATE: &str = "report";

/// The call's script: one request to the test's host.
pub(crate) fn script(release: &Path) -> String {
    let port = std::fs::read_to_string(release.with_file_name(irreversible_net::PORT_FILE))
        .expect("the host port");
    format!("curl -s http://127.0.0.1:{}/ran", port.trim())
}

/// The effect `id` the ledger records for the call of the prompt `tag`
/// in run `run` of `session`, recorded at `at_ms`.
fn ran(id: &str, tag: &str, run: u64, release: &Path, session: &str, at_ms: &Value) -> Value {
    json!({
        "id": id,
        "key": format!("{session}:call-{tag}:0"),
        "run": run,
        "kind": "shellStep",
        "command": script(release),
        "classes": ["net"],
        "sessionId": session,
        "atMs": at_ms,
    })
}

/// The ledger as `get_ran_effects` answers it.
fn ledger(client: &mut WireClient, session_id: &str) -> Vec<Value> {
    let listed = client.request(
        &json!({ "type": "get_ran_effects", "activeSessionId": session_id }),
        WAIT,
    );
    assert_eq!(listed["success"], true, "get_ran_effects: {listed}");
    listed["data"]["effects"]
        .as_array()
        .cloned()
        .unwrap_or_default()
}

#[test]
fn an_effect_is_recorded_once_across_a_restart_and_each_run_reports_its_own() {
    let world = World::new(128_000, &json!({}));
    let listener = TcpListener::bind("127.0.0.1:0").expect("the host");
    let port = listener.local_addr().expect("the host's port").port();
    std::fs::write(
        world.dir.path().join(irreversible_net::PORT_FILE),
        port.to_string(),
    )
    .expect("the port file");
    irreversible_net::serve(
        listener,
        std::sync::Arc::new(std::sync::atomic::AtomicUsize::new(0)),
    );
    let release = world.release_path();

    let mut client = world.connect();
    let session_id = world.create(&mut client, 0);
    let worker = worker_pid(&mut client, &session_id);
    let first = prompt("first", &[TAG], 0);
    client.send(&json!({ "type": "prompt", "activeSessionId": session_id, "message": first }));
    // The step ran unasked and is in the ledger before the model answers.
    let (_, recorded) = client.wait_event_from(0, WAIT, "the effect recorded", |event| {
        event["type"] == "ran_effects_update"
            && event["effects"]
                .as_array()
                .is_some_and(|effects| !effects.is_empty())
    });
    let e1 = recorded["effects"][0].clone();
    let session = e1["sessionId"].as_str().expect("the session id").to_owned();
    assert_eq!(
        recorded["effects"],
        json!([ran("e1", "first", 1, &release, &session, &e1["atMs"])])
    );
    sigkill(worker);
    wait_dead(worker);
    drop(client);

    let mut client = reattach(&world, &session_id);
    world.mock.open_gate(REPORT_GATE);
    wait_idle(&mut client, &session_id);
    let (end, _) = client.wait_event_from(0, WAIT, "the first run's agent_end", |event| {
        event["type"] == "agent_end"
    });
    client.wait_event_from(end, WAIT, "the first run's report", |event| {
        event["type"] == "run_report"
    });
    let quiet = prompt("quiet", &[], 0);
    run_turn(&mut client, &session_id, &quiet);
    let third = prompt("third", &[TAG], 0);
    let before_third = client.len();
    run_turn(&mut client, &session_id, &third);
    let (third_end, _) =
        client.wait_event_from(before_third, WAIT, "the third run's agent_end", |event| {
            event["type"] == "agent_end"
        });
    client.wait_event_from(third_end, WAIT, "the third run's report", |event| {
        event["type"] == "run_report"
    });

    let entries = ledger(&mut client, &session_id);
    let e2 = ran(
        "e2",
        "third",
        3,
        &release,
        &session,
        &entries.get(1).map_or(Value::Null, |e2| e2["atMs"].clone()),
    );
    let e1 = ran("e1", "first", 1, &release, &session, &e1["atMs"]);
    let mut reports: Vec<Value> = client
        .events_from(0)
        .into_iter()
        .filter(|event| event["type"] == "run_report")
        .collect();
    // The step is recorded at its own end, so the kill cut the call
    // after it: the first run also lists the call as treated as not run.
    let cut_at = reports
        .first_mut()
        .map_or(Value::Null, |report| report["unknown"][0]["at"].take());
    let results: Vec<String> = messages_of(&world.transcript(), "toolResult")
        .iter()
        .map(|(_, result)| texts(result).join("\n"))
        .filter_map(|text| text.lines().last().map(str::to_owned))
        .collect();
    assert!(cut_at.is_f64() || cut_at.is_u64(), "{cut_at}");
    let cut = json!({
        "id": "tool:call-first",
        "kind": "tool",
        "what": format!("bash: {}", script(&release)),
        "at": null,
        "cause": "notRepeatSafe",
        "settledRun": 1,
    });
    assert_eq!(
        (entries, reports, results),
        (
            vec![e1.clone(), e2.clone()],
            vec![
                json!({ "type": "run_report", "ran": [e1], "unknown": [cut] }),
                json!({ "type": "run_report", "ran": [e2], "unknown": [] }),
            ],
            // The cut call's result is the interrupted notice (its step's
            // effect is in the ledger and the report).
            vec![
                "</harness>".to_owned(),
                format!("[irreversible: e2 {} (net)]", script(&release)),
            ],
        )
    );
    assert_transcript(&world, &[first, quiet, third]);
}
