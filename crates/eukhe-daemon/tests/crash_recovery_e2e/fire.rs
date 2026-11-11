//! Exactly-once scheduled fires (spec O1-O8): a one-shot cron job fires its
//! prompt into the session as an input whose request id is `cron:<job
//! id>:<run count>`. A real worker is killed (`SIGKILL`) at each point of
//! the fire (`EUKHE_TEST_KILL_AT=fire:<point>`: `intended` once its claim
//! is on record, `started` just before the fire is admitted, `finished`
//! once its result is on record). After the restart, a recovery that
//! clears the dead worker's claim fires the one-shot again under its
//! original request id: the prompt reaches the session exactly once, and
//! the job completes with one run.

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

/// The job `id` of the session's catalog, inactive jobs included (`null`
/// while the catalog lacks it).
fn listed_job(client: &mut WireClient, session_id: &str, id: &str) -> Value {
    let listed = client.request(
        &json!({ "type": "cron_list", "activeSessionId": session_id, "includeInactive": true }),
        WAIT,
    );
    assert_eq!(listed["success"], true, "cron_list: {listed}");
    listed["data"]["jobs"]
        .as_array()
        .expect("the listed jobs")
        .iter()
        .find(|job| job["id"] == id)
        .cloned()
        .unwrap_or(Value::Null)
}

fn fire_killed_at(point: &str) {
    let marks = tempfile::tempdir().expect("marker dir");
    let marker = marks.path().join("killed");
    let world = World::with_env(
        128_000,
        &json!({}),
        &[(
            "EUKHE_TEST_KILL_AT",
            format!("fire:{point}@{}", marker.display()),
        )],
    );
    let mut client = world.connect();
    let session_id = world.create(&mut client, 1);
    let pid = worker_pid(&mut client, &session_id);
    let message = prompt("scheduled", &[], 0);
    let added = client.request(
        &json!({
            "type": "cron_add",
            "activeSessionId": session_id,
            "prompt": message,
            "schedule": "in 1m",
        }),
        WAIT,
    );
    assert_eq!(added["success"], true, "cron_add: {added}");
    let id = added["data"]["job"]["id"]
        .as_str()
        .expect("the job id")
        .to_owned();
    let deadline = Instant::now() + WAIT;
    while !marker.exists() {
        assert!(
            Instant::now() < deadline,
            "fire:{point} was never reached\n{}",
            world.diagnostics()
        );
        std::thread::sleep(Duration::from_millis(20));
    }
    wait_dead(pid);
    drop(client);
    let mut client = reattach(&world, &session_id);
    // The replacement worker's scheduler recovers the dead worker's claim
    // and fires the one-shot again; it completes once its run is recorded.
    let deadline = Instant::now() + WAIT;
    loop {
        let job = listed_job(&mut client, &session_id, &id);
        if job["status"] == "completed" {
            assert_eq!(job["runCount"], 1, "one run of the one-shot: {job}");
            break;
        }
        assert!(
            Instant::now() < deadline,
            "the one-shot never completed: {job}\n{}",
            world.diagnostics()
        );
        std::thread::sleep(Duration::from_millis(100));
    }
    wait_idle(&mut client, &session_id);
    assert_eq!(
        user_entries(&world, &message),
        1,
        "the fire reaches the session once\n{}",
        world.diagnostics()
    );
}

#[test]
fn a_one_shot_killed_once_claimed_fires_once() {
    fire_killed_at("intended");
}

#[test]
fn a_one_shot_killed_before_its_fire_is_admitted_fires_once() {
    fire_killed_at("started");
}

#[test]
fn a_one_shot_killed_once_its_run_is_recorded_fired_once() {
    fire_killed_at("finished");
}
