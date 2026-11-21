use eukhe_durable::types::EntryData;

use super::*;
use crate::durable_test_support::{answer, ask, cx, entries, Fixture, SESSION_ID};
use crate::worker::durable_host::wire_messages::entry_wire_message;

const CAUSE: &str = "The session worker stopped responding for 60s";

/// A turn the supervisor interrupted goes on by itself: three reopens
/// continue it, each with its continuation and its row; the fourth ends
/// the run with its report. A new input starts the count again.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn an_interrupted_turn_continues_three_times_then_ends() {
    let fixture = Fixture::new();
    let session = fixture.open(SESSION_ID).await;
    let main = session.main();
    ask(&fixture, &main, "build it", "started").await;
    fixture
        .faux
        .append_responses(vec![answer("one"), answer("two"), answer("three")]);
    let mut outcomes = Vec::new();
    for reopen in 0..4 {
        let interrupted = Interrupted {
            cause: CAUSE.to_owned(),
            declared_at: format!("declared-{reopen}"),
        };
        outcomes.push(resume(&main, &interrupted, cx()).await.expect("resumed"));
        main.wait_for_idle(cx()).await.expect("idle");
    }
    ask(&fixture, &main, "next task", "on it").await;
    let interrupted = Interrupted {
        cause: CAUSE.to_owned(),
        declared_at: "declared-next".to_owned(),
    };
    fixture.faux.append_responses(vec![answer("again")]);
    outcomes.push(resume(&main, &interrupted, cx()).await.expect("resumed"));
    main.wait_for_idle(cx()).await.expect("idle");

    let transcript = entries(&main).await;
    let inputs: Vec<InputOrigin> = transcript
        .iter()
        .filter(|entry| entry.kind == USER_ENTRY.kind())
        .map(|entry| {
            UserData::decode(entry.data.as_ref())
                .expect("a user entry")
                .origin
        })
        .collect();
    let rows: Vec<serde_json::Value> = transcript
        .iter()
        .filter_map(entry_wire_message)
        .filter(|row| {
            row["customType"] == eukhe_types::custom_type::WORKER_RESTART_NOTICE_CUSTOM_TYPE
        })
        .map(|row| row["content"].clone())
        .collect();
    assert_eq!(
        outcomes,
        [
            Reopened::Continue { n: 1 },
            Reopened::Continue { n: 2 },
            Reopened::Continue { n: 3 },
            Reopened::End { n: 3 },
            Reopened::Continue { n: 1 },
        ]
    );
    assert_eq!(
        inputs,
        [
            InputOrigin::User,
            InputOrigin::RestartResume,
            InputOrigin::RestartResume,
            InputOrigin::RestartResume,
            InputOrigin::User,
            InputOrigin::RestartResume,
        ]
    );
    assert_eq!(
        rows,
        [
            notice(CAUSE, Reopened::Continue { n: 1 }),
            notice(CAUSE, Reopened::Continue { n: 2 }),
            notice(CAUSE, Reopened::Continue { n: 3 }),
            notice(CAUSE, Reopened::End { n: 3 }),
            notice(CAUSE, Reopened::Continue { n: 1 }),
        ]
        .map(serde_json::Value::from)
    );
}

/// A replayed declaration (the reopen's reply was lost) writes no second
/// row and no second continuation.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_replayed_declaration_continues_once() {
    let fixture = Fixture::new();
    let session = fixture.open(SESSION_ID).await;
    let main = session.main();
    ask(&fixture, &main, "build it", "started").await;
    fixture.faux.append_responses(vec![answer("one")]);
    let interrupted = Interrupted {
        cause: CAUSE.to_owned(),
        declared_at: "declared".to_owned(),
    };
    resume(&main, &interrupted, cx()).await.expect("resumed");
    main.wait_for_idle(cx()).await.expect("idle");
    resume(&main, &interrupted, cx()).await.expect("replayed");
    main.wait_for_idle(cx()).await.expect("idle");

    let kinds: Vec<String> = entries(&main)
        .await
        .iter()
        .filter_map(entry_wire_message)
        .filter_map(|row| row["customType"].as_str().map(str::to_owned))
        .collect();
    assert_eq!(
        kinds,
        [
            eukhe_types::custom_type::WORKER_RESTART_NOTICE_CUSTOM_TYPE,
            "restart_resume"
        ]
    );
}
