//! Exactly-once background jobs (spec O1-O9): a user bash command is a
//! job whose start is durable before its process launches, and whose exit
//! is durable before its end retires it. A real worker is killed
//! (`SIGKILL`) at each point of the job's life
//! (`EUKHE_TEST_KILL_AT=job:<point>`: `intended` and `started` once its
//! start record is durable, before the launch; `exited` once its exit is,
//! before its end is; `finished` once its end is). After the restart the
//! model sees exactly one notice for a job whose end was not durable: ran
//! with its exit code when its exit was, else treated as not run (status
//! `interrupted`, one ledger entry); none for one that finished. The
//! command never runs again.

use super::*;

/// The markers of a stale job's notice in the text the model reads.
const INTERRUPTED: &str = " status:interrupted]";
const RAN: &str = " status:ok]";

/// What a restart after a kill at `job:<point>` left: the interrupted-job
/// and the ran-job rows of the transcript, the model requests that carried
/// one, the runs of the command, and the ledger's entries (`(id, cause)`,
/// the job's id written `<job>`).
#[derive(Debug, PartialEq, Eq)]
struct Outcome {
    interrupted: usize,
    ran: usize,
    seen: usize,
    runs: usize,
    noted: Vec<(String, Value)>,
}

fn job_killed_at(point: &str) -> Outcome {
    let marks = tempfile::tempdir().expect("marker dir");
    let marker = marks.path().join("killed");
    let world = World::with_env(
        128_000,
        &json!({}),
        &[(
            "EUKHE_TEST_KILL_AT",
            format!("job:{point}@{}", marker.display()),
        )],
    );
    let mut client = world.connect();
    let session_id = world.create(&mut client, 1);
    let pid = worker_pid(&mut client, &session_id);
    // The file the command appends a line to, once per run.
    let runs = world.dir.path().join("job-runs");
    client.send(&json!({
        "type": "execute_bash",
        "activeSessionId": session_id,
        "command": format!("echo run >> {}", runs.display()),
    }));
    let deadline = Instant::now() + WAIT;
    while !marker.exists() {
        assert!(
            Instant::now() < deadline,
            "job:{point} was never reached\n{}",
            world.diagnostics()
        );
        std::thread::sleep(Duration::from_millis(20));
    }
    wait_dead(pid);
    drop(client);
    let mut client = reattach(&world, &session_id);
    let marker = match point {
        "finished" => None,
        "exited" => Some(RAN),
        _ => Some(INTERRUPTED),
    };
    if let Some(marker) = marker {
        // The notice wakes a turn; the model reads it there.
        world.mock.wait_for(WAIT, "the stale-job notice", |log| {
            log.iter()
                .any(|entry| entry.request.last_user_text.contains(marker))
                .then_some(())
        });
    }
    wait_idle(&mut client, &session_id);
    // One more turn: whatever the reopen admits is in the transcript first.
    run_turn(&mut client, &session_id, &prompt("after", &[], 0));
    let transcript = world.transcript();
    let rows = transcript.custom_rows("job_settled");
    let status_rows = |status: &str| {
        rows.iter()
            .filter(|row| row["details"]["status"] == status)
            .count()
    };
    let seen = world
        .mock
        .log()
        .iter()
        .filter(|entry| {
            entry.request.kind == RequestKind::Turn
                && (entry.request.last_user_text.contains(INTERRUPTED)
                    || entry.request.last_user_text.contains(RAN))
        })
        .count();
    let jobs: Vec<String> = rows
        .iter()
        .filter_map(|row| row["details"]["job"].as_str())
        .map(|job| format!("job:{job}"))
        .collect();
    let listed = client.request(
        &json!({ "type": "get_unknown_effects", "activeSessionId": session_id }),
        WAIT,
    );
    assert_eq!(listed["success"], true, "get_unknown_effects: {listed}");
    let noted = listed["data"]["effects"]
        .as_array()
        .map(|effects| {
            effects
                .iter()
                .map(|effect| {
                    let id = effect["id"].as_str().unwrap_or_default();
                    let id = if jobs.iter().any(|job| job == id) {
                        "job:<job>".to_owned()
                    } else {
                        id.to_owned()
                    };
                    (id, effect["cause"].clone())
                })
                .collect()
        })
        .unwrap_or_default();
    let runs = std::fs::read_to_string(&runs).map_or(0, |runs| runs.lines().count());
    Outcome {
        interrupted: status_rows("interrupted"),
        ran: status_rows("ok"),
        seen,
        runs,
        noted,
    }
}

/// A job treated as not run: one interrupted notice, one ledger entry,
/// never run.
fn treated_as_not_run() -> Outcome {
    Outcome {
        interrupted: 1,
        ran: 0,
        seen: 1,
        runs: 0,
        noted: vec![("job:<job>".to_owned(), json!("notRepeatSafe"))],
    }
}

#[test]
fn a_job_killed_once_intended_is_treated_as_not_run_once_and_never_runs() {
    assert_eq!(job_killed_at("intended"), treated_as_not_run());
}

#[test]
fn a_job_killed_once_started_is_treated_as_not_run_once_and_never_runs() {
    assert_eq!(job_killed_at("started"), treated_as_not_run());
}

#[test]
fn a_job_killed_once_exited_is_reported_ran_once_and_ran_once() {
    assert_eq!(
        job_killed_at("exited"),
        Outcome {
            interrupted: 0,
            ran: 1,
            seen: 1,
            runs: 1,
            noted: Vec::new(),
        }
    );
}

#[test]
fn a_job_killed_once_finished_is_not_reported_and_ran_once() {
    assert_eq!(
        job_killed_at("finished"),
        Outcome {
            interrupted: 0,
            ran: 0,
            seen: 0,
            runs: 1,
            noted: Vec::new(),
        }
    );
}
