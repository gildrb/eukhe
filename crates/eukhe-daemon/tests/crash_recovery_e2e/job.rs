//! Exactly-once background jobs (spec O1-O8): a user bash command is a
//! job whose start is durable before its process launches. A real worker
//! is killed (`SIGKILL`) at each point of the job's life
//! (`EUKHE_TEST_KILL_AT=job:<point>`: `intended` and `started` once its
//! start record is durable, before the launch; `finished` once its end
//! is). After the restart the model sees exactly one interrupted notice
//! for a job whose end was not durable and none for one that finished,
//! and the command never runs again.

use super::*;

/// The marker of an interrupted job in the text the model reads.
const INTERRUPTED: &str = " status:interrupted]";

/// What a restart after a kill at `job:<point>` left: the interrupted-job
/// rows of the transcript, the model requests that carried one, and the
/// runs of the command.
#[derive(Debug, PartialEq, Eq)]
struct Outcome {
    rows: usize,
    seen: usize,
    runs: usize,
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
    if point != "finished" {
        // The notice wakes a turn; the model reads it there.
        world
            .mock
            .wait_for(WAIT, "the interrupted-job notice", |log| {
                log.iter()
                    .any(|entry| entry.request.last_user_text.contains(INTERRUPTED))
                    .then_some(())
            });
    }
    wait_idle(&mut client, &session_id);
    // One more turn: whatever the reopen admits is in the transcript first.
    run_turn(&mut client, &session_id, &prompt("after", &[], 0));
    let rows = world
        .transcript()
        .custom_rows("job_settled")
        .iter()
        .filter(|row| row["details"]["status"] == "interrupted")
        .count();
    let seen = world
        .mock
        .log()
        .iter()
        .filter(|entry| {
            entry.request.kind == RequestKind::Turn
                && entry.request.last_user_text.contains(INTERRUPTED)
        })
        .count();
    let runs = std::fs::read_to_string(&runs).map_or(0, |runs| runs.lines().count());
    Outcome { rows, seen, runs }
}

#[test]
fn a_job_killed_once_intended_is_reported_interrupted_once_and_never_runs() {
    assert_eq!(
        job_killed_at("intended"),
        Outcome {
            rows: 1,
            seen: 1,
            runs: 0
        }
    );
}

#[test]
fn a_job_killed_once_started_is_reported_interrupted_once_and_never_runs() {
    assert_eq!(
        job_killed_at("started"),
        Outcome {
            rows: 1,
            seen: 1,
            runs: 0
        }
    );
}

#[test]
fn a_job_killed_once_finished_is_not_reported_and_ran_once() {
    assert_eq!(
        job_killed_at("finished"),
        Outcome {
            rows: 0,
            seen: 0,
            runs: 1
        }
    );
}
